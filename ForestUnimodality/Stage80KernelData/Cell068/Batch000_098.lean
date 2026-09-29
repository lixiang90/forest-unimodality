import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell068.Parameters
import ForestUnimodality.BinomialMassData.Q24_49.Batch000_049
import ForestUnimodality.BinomialMassData.Q24_49.Batch050_099
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch000_049
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree000.table
  base := (418919755875240706244255759/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (550834685334023604896813700000000000000)
      linear := (10662622954262400074010308500000000000)
      constant := (209459877937620353122127879500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree000.table
  base := (418919755875240706244255759/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (550834685334023604896813700000000000000)
      linear := (10662622954262400074010308500000000000)
      constant := (209459877937620353122127879500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree001.table
  base := (48650772200195306424245341936526567504459/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-2539924444384878992279214143383000000000000)
      constant := (584662003331661023650932387084809442891030295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree001.table
  base := (121395771652890179718248357436142227872671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-4160100325980013786002073150127380500000000000)
      constant := (953237509630644311065242162118235165587498792957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24994793293705898961/50000000000000000000)
  directionHi := (49989586587411797923/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree002.table
  base := (145427019827047642767551386785756984287721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-5131050804196126029713825788183000000000000)
      constant := (351658363856383720726307252711018519274818121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree002.table
  base := (72456186595071399444734442220415952807867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-8403838980808999773765488118819430500000000000)
      constant := (572437102233378965924035246941030356443746875089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24994793293705898961/50000000000000000000)
  centralHi := (49989586587411797923/100000000000000000000)
  directionLo := (17673987832335482587/25000000000000000000)
  directionHi := (70695951329341930349/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree003.table
  base := (45082498691956863161596554678031637782913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-3861088582003686533574218716491500000000000)
      constant := (111060988634377369071317301634365962316774113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree003.table
  base := (44864456322112159999101785581079013087361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (480087130853777615154681638813100000000000000)
      linear := (-1405286403959776195725433676390164500000000000)
      constant := (40130525728290387566135336615492483258459615243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17673987832335482587/25000000000000000000)
  centralHi := (70695951329341930349/100000000000000000000)
  directionLo := (17316900763752184271/20000000000000000000)
  directionHi := (21646125954690230339/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree004.table
  base := (58271210112824068652078585586188004862819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-10313303523818620104583049077783000000000000)
      constant := (149961846444213611259202465128469399675628419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree004.table
  base := (14483829455155383524676534809689718766541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-16891316290466971749292318056203530500000000000)
      constant := (243732231279062899225083304495331465931809924494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17316900763752184271/20000000000000000000)
  centralHi := (21646125954690230339/25000000000000000000)
  directionLo := (24994793293705898961/25000000000000000000)
  directionHi := (19995834634964719169/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree005.table
  base := (39292137596828566479883199937810282499281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-12904429883629867142017660722583000000000000)
      constant := (110079068861663142114357436382722488280773681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree005.table
  base := (19520793275436102218161908560807078832921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-21135054945295957737055733024895580500000000000)
      constant := (178967461486945663276951620925623218564714129707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24994793293705898961/25000000000000000000)
  centralHi := (19995834634964719169/20000000000000000000)
  directionLo := (2235602275531290259/2000000000000000000)
  directionHi := (111780113776564512951/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree006.table
  base := (3439115801013799751258912130883016444229/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-7747778121720557089726136183691500000000000)
      constant := (44376140720457570787308704251424489930375316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree006.table
  base := (2732539903424463775446900925428325147763/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (160029043617925871718227212937700000000000000)
      linear := (-939955318523146063882190666429171500000000000)
      constant := (5349529341558472399509716050870235001266272615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2235602275531290259/2000000000000000000)
  centralHi := (111780113776564512951/100000000000000000000)
  directionLo := (122448979591836734693/100000000000000000000)
  directionHi := (61224489795918367347/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree007.table
  base := (9905051718139917372254731079882400098097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2058)
      previous := (1029)
      next := (1029)
      square := (26990899581367156639943871300000000000000)
      linear := (-184557985747473073641702898083500000000000)
      constant := (800836992284937464448612782286237604806753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree007.table
  base := (19665891920172351949728768423407174128959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (13446972)
      previous := (6723486)
      next := (6723486)
      square := (176358537864653001485393255074200000000000000)
      linear := (-1209082949181793049493165835195089000000000000)
      constant := (5220473178555844366031812185078582406086143597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122448979591836734693/100000000000000000000)
  centralHi := (61224489795918367347/50000000000000000000)
  directionLo := (66130007126610818683/50000000000000000000)
  directionHi := (132260014253221637367/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree008.table
  base := (14468232087795401824143750768662404607353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-20677808963063608254321495656983000000000000)
      constant := (75149537009596250801808848104422433462254553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree008.table
  base := (14352636764856466237532437277257265908717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-67732541819565831400691955861943461000000000000)
      constant := (245304011577263764240820830315817808024792032039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66130007126610818683/50000000000000000000)
  centralHi := (132260014253221637367/100000000000000000000)
  directionLo := (17673987832335482587/12500000000000000000)
  directionHi := (141391902658683860697/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree009.table
  base := (2634875466077781130365017389971033357271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-11634467661437427645878053650891500000000000)
      constant := (38239561865701797055695228388676902181615342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree009.table
  base := (10442470251870091217068507896960797089297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (320058087235851743436454425875400000000000000)
      linear := (-2822963671452733458378473548123243000000000000)
      constant := (9258475025268331830657609037082453481179653737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17673987832335482587/12500000000000000000)
  centralHi := (141391902658683860697/100000000000000000000)
  directionLo := (149968759762235393767/100000000000000000000)
  directionHi := (18746094970279424221/12500000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree010.table
  base := (7495446890076181734878448483594467760027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-25860061682686102329190718946583000000000000)
      constant := (81201938841668179979815370593190317091824827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree010.table
  base := (3705238819861658051853669357644322619941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-42353748219440887675872807868355830500000000000)
      constant := (132855080831322709738852579742872802550432740047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149968759762235393767/100000000000000000000)
  centralHi := (18746094970279424221/12500000000000000000)
  directionLo := (79040476453212589493/50000000000000000000)
  directionHi := (158080952906425178987/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree011.table
  base := (5037235095491602985230338481222560736317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-28451188042497349366625330591383000000000000)
      constant := (88600486541282880286599903262303368327897117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree011.table
  base := (1240074107142007243824736211269206313679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 324135000000000000000000000000000000000000000
      center := (2722734)
      previous := (1361367)
      next := (1361367)
      square := (35708960146148748234645741729900000000000000)
      linear := (-385103197308015484823439858157420500000000000)
      constant := (1199063356253591176238953352336670050393737066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79040476453212589493/50000000000000000000)
  centralHi := (158080952906425178987/100000000000000000000)
  directionLo := (82898351067713881229/50000000000000000000)
  directionHi := (165796702135427762459/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree012.table
  base := (598449657503037867322502645310387038951/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-31042314402308596404059942236183000000000000)
      constant := (98260310548753375386640408375447196402606755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree012.table
  base := (365116074555226367719085880256721868403/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (480087130853777615154681638813100000000000000)
      linear := (-5649025058788762183488848645082214500000000000)
      constant := (17890389855181956093787971613084243627163695556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82898351067713881229/50000000000000000000)
  centralHi := (165796702135427762459/100000000000000000000)
  directionLo := (17316900763752184271/10000000000000000000)
  directionHi := (173169007637521842711/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree013.table
  base := (251527553116264024390840299100512043081/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-33633440762119843441494553880983000000000000)
      constant := (109934471134021610058299964223605647077187405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree013.table
  base := (1190543934410758240304285062070976936611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-110169928367855691278326105548863961000000000000)
      constant := (360472454220862314906100373353994976096231436937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17316900763752184271/10000000000000000000)
  centralHi := (173169007637521842711/100000000000000000000)
  directionLo := (180240017680160139893/100000000000000000000)
  directionHi := (90120008840080069947/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree014.table
  base := (-46106511805854108080662041490304226361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4116)
      previous := (2058)
      next := (2058)
      square := (53981799162734313279887742600000000000000)
      linear := (-739276880039410009774064602567000000000000)
      constant := (2519784852001482182035020402122875464541555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree014.table
  base := (-147088190546036189786341313448935438171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800415000000000000000000000000000000000000000
      center := (6723486)
      previous := (3361743)
      next := (3361743)
      square := (88179268932326500742696627537100000000000000)
      linear := (-1210789853852180237284213627410694500000000000)
      constant := (4132785363282756106747452331157683318251271807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180240017680160139893/100000000000000000000)
  centralHi := (90120008840080069947/50000000000000000000)
  directionLo := (46760976479141224557/25000000000000000000)
  directionHi := (187043905916564898229/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree015.table
  base := (-1514195609897617548712191230146070186303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-38815693481742337516363777170583000000000000)
      constant := (138764589441388361180185056212539285482686497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree015.table
  base := (-393701177792716076122989377156402921923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (160029043617925871718227212937700000000000000)
      linear := (-2354534870132808059803328989326521500000000000)
      constant := (8431897317592021331273115981749939958440016234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46760976479141224557/25000000000000000000)
  centralHi := (187043905916564898229/100000000000000000000)
  directionLo := (96804418168419775469/50000000000000000000)
  directionHi := (193608836336839550939/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree016.table
  base := (-81955662383541356062751966386226742409/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-20703409920776792276899194407691500000000000)
      constant := (77874842720980258629365303441770713463615856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree016.table
  base := (-1340184649830619103531403208135914467791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-67816180148414803602453297680508130500000000000)
      constant := (255586611688050264823031011588472379808378054003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96804418168419775469/50000000000000000000)
  centralHi := (193608836336839550939/100000000000000000000)
  directionLo := (199958346349647191689/100000000000000000000)
  directionHi := (19995834634964719169/10000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree017.table
  base := (-894339915137022292654889324260188633589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-21998973100682415795616500230091500000000000)
      constant := (87186357628853310413934803134170574181505622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree017.table
  base := (-145297383093145416247152850283463214971/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-144119837606487579180433425298400361000000000000)
      constant := (572396117440363248743221908149669731993301823575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199958346349647191689/100000000000000000000)
  centralHi := (19995834634964719169/10000000000000000000)
  directionLo := (103056172840429366871/50000000000000000000)
  directionHi := (206112345680858733743/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree018.table
  base := (-1098877877601829486067235733361410451163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-23294536280588039314333806052491500000000000)
      constant := (97296454344837009563401443746870507013515274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree018.table
  base := (-4447930964204857109634723686896850243921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (320058087235851743436454425875400000000000000)
      linear := (-5652122774672057450220750193917943000000000000)
      constant := (23661419777544063643540933296963476670285827159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103056172840429366871/50000000000000000000)
  centralHi := (206112345680858733743/100000000000000000000)
  directionLo := (53021963497006447761/25000000000000000000)
  directionHi := (42417570797605158209/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree019.table
  base := (-1018189993203305151625502595554651073409/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-49180198920987325666102223749783000000000000)
      constant := (216376860096245308135876175720518413863724955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree019.table
  base := (-5140752984828634037003947823944199518543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-161094792225803523131487085173168561000000000000)
      constant := (710450883454664990683919667138404447465180965619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53021963497006447761/25000000000000000000)
  centralHi := (42417570797605158209/20000000000000000000)
  directionLo := (27237444520488038803/12500000000000000000)
  directionHi := (8715982246556172417/4000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree020.table
  base := (-5675457164437531679154790516770713677009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-51771325280798572703536835394583000000000000)
      constant := (239696280566335060275319656017393516461501391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree020.table
  base := (-143067020496185531132205843624224067551/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-84791134767730747553506957555276330500000000000)
      constant := (393540680648509162410777422116152569322348601660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27237444520488038803/12500000000000000000)
  centralHi := (8715982246556172417/4000000000000000000)
  directionLo := (2235602275531290259/1000000000000000000)
  directionHi := (223560227553129025901/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree021.table
  base := (-6159240564959123586170825751065786038533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4116)
      previous := (2058)
      next := (2058)
      square := (53981799162734313279887742600000000000000)
      linear := (-1109437788583873872264723408967000000000000)
      constant := (5398503305922263180573191588829776484111883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree021.table
  base := (-3101964063262913526549316818644699935999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88935000000000000000000000000000000000000000
      center := (747054)
      previous := (373527)
      next := (373527)
      square := (9797696548036277860299625281900000000000000)
      linear := (-201893137012607105535760481913760500000000000)
      constant := (984886225520239338331710079367227847238385787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2235602275531290259/1000000000000000000)
  centralHi := (223560227553129025901/100000000000000000000)
  directionLo := (229081064496363758301/100000000000000000000)
  directionHi := (114540532248181879151/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree022.table
  base := (-3275638702014594508157395693329737220249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-28476789000210533389203029342091500000000000)
      constant := (145423225011550718438752608779603300934182151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree022.table
  base := (-6593481602527668683664784899387305824353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (5445468)
      previous := (2722734)
      next := (2722734)
      square := (71417920292297496469291483459800000000000000)
      linear := (-1541795240948573876512955165167941000000000000)
      constant := (7893762479599831236943741919898983625324668069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229081064496363758301/100000000000000000000)
  centralHi := (114540532248181879151/50000000000000000000)
  directionLo := (117235972378327115507/50000000000000000000)
  directionHi := (46894388951330846203/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree023.table
  base := (-6859539318584495130548154753397029893413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-59544704360232313815840670328983000000000000)
      constant := (318636504764781505410107662078077731225915387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree023.table
  base := (-431207682978266446737687537294316727097/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-97522350732217705516797202461352480500000000000)
      constant := (523222789917042692709672703385807232862443332008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117235972378327115507/50000000000000000000)
  centralHi := (46894388951330846203/20000000000000000000)
  directionLo := (11987081759664010803/5000000000000000000)
  directionHi := (239741635193280216061/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree024.table
  base := (-7091147869803096974938748985292026129879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-62135830720043560853275281973783000000000000)
      constant := (347879727346842591280284854054505845262160521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree024.table
  base := (-7128582904545347754477838263120190565491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (320058087235851743436454425875400000000000000)
      linear := (-7538228843484940111448934624447743000000000000)
      constant := (42315358363801910108892907536015241116722989189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11987081759664010803/5000000000000000000)
  centralHi := (239741635193280216061/100000000000000000000)
  directionLo := (244897959183673469387/100000000000000000000)
  directionHi := (61224489795918367347/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree025.table
  base := (-1813122263793160485427830187739819594581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-32363478539927403945354946809291500000000000)
      constant := (189280392494658426549652588368573386306822038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree025.table
  base := (-3643827667729014108937141316404703422969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-106009828041875677492324032398736580500000000000)
      constant := (621651197292017859093166095880607272860101825077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244897959183673469387/100000000000000000000)
  centralHi := (61224489795918367347/25000000000000000000)
  directionLo := (249947932937058989611/100000000000000000000)
  directionHi := (62486983234264747403/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree026.table
  base := (-3674651243941724230961932986913382180551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-33659041719833027464072252631691500000000000)
      constant := (205332948440467168157099190956924969384497049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree026.table
  base := (-7382285985526775922125723259491597027983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-220507133393409326960174894734857261000000000000)
      constant := (1348763665951541075477291427041583950475500473139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249947932937058989611/100000000000000000000)
  centralHi := (62486983234264747403/25000000000000000000)
  directionLo := (254897877485648906361/100000000000000000000)
  directionHi := (127448938742824453181/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree027.table
  base := (-7386754107166108938714448762158288435323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-69909209799477301965579116908183000000000000)
      constant := (444182659601602388565029977660673949466789477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree027.table
  base := (-7417645302868303491478915186647507006457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (320058087235851743436454425875400000000000000)
      linear := (-8481281877891381442063026839712643000000000000)
      constant := (54031775280878523228468475489624771866977105903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254897877485648906361/100000000000000000000)
  centralHi := (127448938742824453181/50000000000000000000)
  directionLo := (51950702291256552813/20000000000000000000)
  directionHi := (129876755728141382033/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree028.table
  base := (-460593595457101628303388171364563934427/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2058)
      previous := (1029)
      next := (1029)
      square := (26990899581367156639943871300000000000000)
      linear := (-739799348564168867377691107683500000000000)
      constant := (4888774487993913371584371968713090937704616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree028.table
  base := (-7398389891156980202141577347583154068887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (13446972)
      previous := (6723486)
      next := (6723486)
      square := (176358537864653001485393255074200000000000000)
      linear := (-4846573224749495324718950094073989000000000000)
      constant := (32113238117742013764797746368694862947190362379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51950702291256552813/20000000000000000000)
  centralHi := (129876755728141382033/50000000000000000000)
  directionLo := (264520028506443274733/100000000000000000000)
  directionHi := (132260014253221637367/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree029.table
  base := (-3650863526311605511698927051970662158489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-37545731259549898020224170098891500000000000)
      constant := (257703773510860048863981733886334440157467911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree029.table
  base := (-7328715698150523344169844474164469366717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-245969565322383242886755384547009561000000000000)
      constant := (1692802958213116683206354873982338883518024281961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264520028506443274733/100000000000000000000)
  centralHi := (132260014253221637367/50000000000000000000)
  directionLo := (16825135150858315269/6250000000000000000)
  directionHi := (53840432482746608861/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree030.table
  base := (-7187224223829048990347832365032240358231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-77682588878911043077882951842583000000000000)
      constant := (553096521717249371981969131283797590899887369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree030.table
  base := (-7212404750381633395257149062512041303679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (960174261707555230309363277626200000000000000)
      linear := (-28273004736893468318031357164932629000000000000)
      constant := (201843459716163985902720606001021500245241619723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16825135150858315269/6250000000000000000)
  centralHi := (53840432482746608861/20000000000000000000)
  directionLo := (273804242142831391397/100000000000000000000)
  directionHi := (136902121071415695699/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree031.table
  base := (-7029399104971924380828837001534608678393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-80273715238722290115317563487383000000000000)
      constant := (592158636346229409767759059232363404563178407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree031.table
  base := (-3526433312069529998778699315462500199447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-131472259970849593418904522210888880500000000000)
      constant := (972443230260792840345100018630635017323024369051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273804242142831391397/100000000000000000000)
  centralHi := (136902121071415695699/50000000000000000000)
  directionLo := (55666047742799411807/20000000000000000000)
  directionHi := (69582559678499264759/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree032.table
  base := (-6831327141528899553378468538862784002463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-82864841598533537152752175132183000000000000)
      constant := (632586506764069784362484472756846455610086337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree032.table
  base := (-6853175474229967321083396955119569734131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-271431997251357158813335874359161861000000000000)
      constant := (2077664813565170338073918800063997453994304249223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55666047742799411807/20000000000000000000)
  centralHi := (69582559678499264759/25000000000000000000)
  directionLo := (17673987832335482587/6250000000000000000)
  directionHi := (282783805317367721393/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree033.table
  base := (-6595782196851754832165023190248507092431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-85455967958344784190186786776983000000000000)
      constant := (674373472924862871207817292649277334471073169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree033.table
  base := (-3308051611798003391603624974841189771381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-42840446060761421914426492852241500000000000)
      constant := (338981397830877975890286192178185178358914219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17673987832335482587/6250000000000000000)
  centralHi := (282783805317367721393/100000000000000000000)
  directionLo := (143584155912962129221/50000000000000000000)
  directionHi := (287168311825924258443/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree034.table
  base := (-6325266236390590525159393194835293089347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-88047094318156031227621398421783000000000000)
      constant := (717513527609562979464319406643472461292477853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree034.table
  base := (-6344149382228840631402008305920680505467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-288406951870673102764389534233930061000000000000)
      constant := (2356585773783102981759284385829053146929522985711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143584155912962129221/50000000000000000000)
  centralHi := (287168311825924258443/100000000000000000000)
  directionLo := (145743437317201020367/50000000000000000000)
  directionHi := (58297374926880408147/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree035.table
  base := (-6022036040324691872098949761330026123407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4116)
      previous := (2058)
      next := (2058)
      square := (53981799162734313279887742600000000000000)
      linear := (-1849759605672801597246041021767000000000000)
      constant := (15551045965080809087171048703414828719953057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree035.table
  base := (-6039567876532046315572388843056014035819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (13446972)
      previous := (6723486)
      next := (6723486)
      square := (176358537864653001485393255074200000000000000)
      linear := (-6059069983272062749794211513700289000000000000)
      constant := (51075328462936458559053883186293272855103987023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145743437317201020367/50000000000000000000)
  centralHi := (58297374926880408147/20000000000000000000)
  directionLo := (295742382575294664769/100000000000000000000)
  directionHi := (29574238257529466477/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree036.table
  base := (-5688127264402554100970032251908044662879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-93229347037778525302490621711383000000000000)
      constant := (807831759353600731586608031312256784764427521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree036.table
  base := (-44565556329836508896125981649540551831/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (160029043617925871718227212937700000000000000)
      linear := (-5655220490555352716952651742753671500000000000)
      constant := (49133416167296316893268041710067691577856387136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295742382575294664769/100000000000000000000)
  centralHi := (29574238257529466477/10000000000000000000)
  directionLo := (149968759762235393767/50000000000000000000)
  directionHi := (59987503904894157507/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree037.table
  base := (-5325376124538159871263468290143400001947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-95820473397589772339925233356183000000000000)
      constant := (855000640049076766044561864054061696595325253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree037.table
  base := (-5340452233900615964314012663928086537373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-313869383799647018690970024046082361000000000000)
      constant := (2808111531830455628861804727233364794269048184009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149968759762235393767/50000000000000000000)
  centralHi := (59987503904894157507/20000000000000000000)
  directionLo := (304074784199006933047/100000000000000000000)
  directionHi := (38009348024875866631/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree038.table
  base := (-4935438946614594704804141823903157566777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-98411599757401019377359845000983000000000000)
      constant := (903503917536942460307341338333912518682168423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree038.table
  base := (-4949403766494125704378186550599868092037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-322356861109304990666496853983466461000000000000)
      constant := (2967399306250922666846879782363269124994899605521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304074784199006933047/100000000000000000000)
  centralHi := (38009348024875866631/12500000000000000000)
  directionLo := (308156507562071416213/100000000000000000000)
  directionHi := (154078253781035708107/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree039.table
  base := (-2259904897694381458164965655024540842189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-50501363058606133207397228322891500000000000)
      constant := (476669002283858243557630403988442077437904211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree039.table
  base := (-1133184070994629698394083342137699397571/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (480087130853777615154681638813100000000000000)
      linear := (-18380241023275720146779093551158364500000000000)
      constant := (173947561383442317505037268708900105474909653054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308156507562071416213/100000000000000000000)
  centralHi := (154078253781035708107/50000000000000000000)
  directionLo := (156092434089575045817/50000000000000000000)
  directionHi := (62436973635830018327/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree040.table
  base := (-2039918186645388996471213844981750855311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-51796926238511756726114534145291500000000000)
      constant := (502249832653932071992894676566358816196398289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree040.table
  base := (-12786855836882501472845462201851211083/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-169665907864310467308775256929117330500000000000)
      constant := (1649535692359318228519378409488031447197408870240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156092434089575045817/50000000000000000000)
  centralHi := (62436973635830018327/20000000000000000000)
  directionLo := (316161905812850357973/100000000000000000000)
  directionHi := (158080952906425178987/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree041.table
  base := (-45209179500506135595193099654798154587/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-53092489418417380244831839967691500000000000)
      constant := (528492990455189034438438419581717185233464520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree041.table
  base := (-3627788585242776328982073925437459149931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-347819293038278906593077343795618761000000000000)
      constant := (3471435638164017553272811749021424373368178190623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316161905812850357973/100000000000000000000)
  centralHi := (158080952906425178987/50000000000000000000)
  directionLo := (320089533497104529269/100000000000000000000)
  directionHi := (32008953349710452927/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree042.table
  base := (-1565800173305201107883938112562306226549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2058)
      previous := (1029)
      next := (1029)
      square := (26990899581367156639943871300000000000000)
      linear := (-1109960257108632729868349914083500000000000)
      constant := (11334635902656462117579413524716446994899099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree042.table
  base := (-1570906728236014660221624948513933581341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (249018)
      previous := (124509)
      next := (124509)
      square := (3265898849345425953433208427300000000000000)
      linear := (-134658643366567225460545795061603500000000000)
      constant := (1378737827480967679649720323455314137796229211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320089533497104529269/100000000000000000000)
  centralHi := (32008953349710452927/10000000000000000000)
  directionLo := (80992387073405834403/25000000000000000000)
  directionHi := (323969548293623337613/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree043.table
  base := (-2625423501667104009077337581182594335791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-111367231556457254564532903224983000000000000)
      constant := (1165922302963761312743568433964724590999765809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree043.table
  base := (-2634854147552534735032536117196574269827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-364794247657594850544131003670386961000000000000)
      constant := (3829177613139872340331086231247031686007000933591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80992387073405834403/25000000000000000000)
  centralHi := (323969548293623337613/100000000000000000000)
  directionLo := (81950910225556176227/25000000000000000000)
  directionHi := (327803640902224704909/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree044.table
  base := (-524774023723853787492189710088466508719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-56979178958134250800983757434891500000000000)
      constant := (611183896040574447153246157772331183825131362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree044.table
  base := (-526949878679685946651845171450630409433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 324135000000000000000000000000000000000000000
      center := (2722734)
      previous := (1361367)
      next := (1361367)
      square := (35708960146148748234645741729900000000000000)
      linear := (-1542486466806829845122553031437070500000000000)
      constant := (16589010871040730289987030429049254464895373818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81950910225556176227/25000000000000000000)
  centralHi := (327803640902224704909/100000000000000000000)
  directionLo := (82898351067713881229/25000000000000000000)
  directionHi := (331593404270855524917/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree045.table
  base := (-388355747328674339088664703729381879233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-58274742138039874319701063257291500000000000)
      constant := (640064426668193272363423106246871508215923134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree045.table
  base := (-312290222578428722994625861050341669821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (320058087235851743436454425875400000000000000)
      linear := (-14139600084330029425747580131302043000000000000)
      constant := (155711965074817975000970884257910747188709666295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82898351067713881229/25000000000000000000)
  centralHi := (331593404270855524917/100000000000000000000)
  directionLo := (335340341329693538851/100000000000000000000)
  directionHi := (83835085332423384713/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree046.table
  base := (-989130203655253978523841062938018425439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-119140610635890995676836738159383000000000000)
      constant := (1339203743558502805660586707469053817760520961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree046.table
  base := (-249132942556363159692396649405668036923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-195128339793284383235355746741269630500000000000)
      constant := (2199109610956049357685599544162774868727235028318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335340341329693538851/100000000000000000000)
  centralHi := (83835085332423384713/25000000000000000000)
  directionLo := (339045871955839789901/100000000000000000000)
  directionHi := (169522935977919894951/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree047.table
  base := (-101718158982392820996883108709662929863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-60865868497851121357135674902091500000000000)
      constant := (699795445168684848789709672401364198610797874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree047.table
  base := (-4136933204436851641310454216627332701/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-199372078448113369223119161709961680500000000000)
      constant := (2298262006220242514709270549867081377288103251650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339045871955839789901/100000000000000000000)
  centralHi := (169522935977919894951/50000000000000000000)
  directionLo := (342711339260136024529/100000000000000000000)
  directionHi := (34271133926013602453/10000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree048.table
  base := (192758969612186414131737030567796169647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-124322863355513489751705961448983000000000000)
      constant := (1461288875296042575967536929871577278603322447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree048.table
  base := (186476424280127460132114107177513108199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (960174261707555230309363277626200000000000000)
      linear := (-45247959356209412269085017039700829000000000000)
      constant := (533236979751908399297230101918707446857121245037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342711339260136024529/100000000000000000000)
  centralHi := (34271133926013602453/10000000000000000000)
  directionLo := (17316900763752184271/5000000000000000000)
  directionHi := (346338015275043685421/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree049.table
  base := (202307934503493397000531535456753336679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (550834685334023604896813700000000000000)
      linear := (-26429402273078870634973047291500000000000)
      constant := (317429491670502285612789506866913506673358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree049.table
  base := (401723692656058183929410217086504037707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (137214)
      previous := (68607)
      next := (68607)
      square := (1799576916986255117197890357900000000000000)
      linear := (-86572076533848955101476881152580500000000000)
      constant := (1042490937092846953828697847326344233691188769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17316900763752184271/5000000000000000000)
  centralHi := (346338015275043685421/100000000000000000000)
  directionLo := (21870444131992661591/6250000000000000000)
  directionHi := (349927106111882585457/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree050.table
  base := (721032497385677679208968375927956654873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-64752558037567991913287592369291500000000000)
      constant := (794306183677506374034840654930803023928350073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree050.table
  base := (1436741547137354786704517287923617770867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-424206588825200654372818813232075661000000000000)
      constant := (5217246249312785340147185090034243886177071396089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21870444131992661591/6250000000000000000)
  centralHi := (349927106111882585457/100000000000000000000)
  directionLo := (17673987832335482587/5000000000000000000)
  directionHi := (353479756646709651741/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree051.table
  base := (52270628807641425674406097044916180219/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-66048121217473615432004898191691500000000000)
      constant := (827117839656024247843934900328700874974116380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree051.table
  base := (521481960967914218939092338369560745751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (160029043617925871718227212937700000000000000)
      linear := (-8012853076571456043487882280915921500000000000)
      constant := (100606365641412989431182099581802613439832652542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17673987832335482587/5000000000000000000)
  centralHi := (353479756646709651741/100000000000000000000)
  directionLo := (89249263696611741901/25000000000000000000)
  directionHi := (71399410957289393521/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree052.table
  base := (2755121097355075146466447211022898997453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-134687368794758477901444408028183000000000000)
      constant := (1721165415809917628290428032992481980492884653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree052.table
  base := (1375308774002052360093849145786977179541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-220590771722258299161936236553421930500000000000)
      constant := (2826265458342879478169975583364884790223790633247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89249263696611741901/25000000000000000000)
  centralHi := (71399410957289393521/20000000000000000000)
  directionLo := (180240017680160139893/50000000000000000000)
  directionHi := (360480035360320279787/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree053.table
  base := (686920006042558928140374430731190910319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-137278495154569724938879019672983000000000000)
      constant := (1789400729776524082879431801186151946878379595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree053.table
  base := (3430460112042324797381292016082365053571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-449669020754174570299399303044227961000000000000)
      constant := (5876605015743141061415103031014728413248669513257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180240017680160139893/50000000000000000000)
  centralHi := (360480035360320279787/100000000000000000000)
  directionLo := (90982420919015346343/25000000000000000000)
  directionHi := (363929683676061385373/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree054.table
  base := (2064471855774703833512682407347468794017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-69934810757190485988156815658891500000000000)
      constant := (929470428559618975612330639368257272574434817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree054.table
  base := (4125139418577734668095831396119137249631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (320058087235851743436454425875400000000000000)
      linear := (-16968759187549353417589856777096743000000000000)
      constant := (226109761561567220647439134586710337372900047751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90982420919015346343/25000000000000000000)
  centralHi := (363929683676061385373/100000000000000000000)
  directionLo := (367346938775510204081/100000000000000000000)
  directionHi := (183673469387755102041/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree055.table
  base := (967573015378611405185000280431700654383/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-142460747874192219013748242962583000000000000)
      constant := (1929785108596262304190088336619022566355867915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree055.table
  base := (2417185199328553393543745998394727168713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 324135000000000000000000000000000000000000000
      center := (2722734)
      previous := (1361367)
      next := (1361367)
      square := (35708960146148748234645741729900000000000000)
      linear := (-1928280889973101298555590755863620500000000000)
      constant := (26188447602658313668620140020684171853166157651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367346938775510204081/100000000000000000000)
  centralHi := (183673469387755102041/50000000000000000000)
  directionLo := (74146539284020204051/20000000000000000000)
  directionHi := (11585396763128156883/3125000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree056.table
  base := (695138147843997562592740104885016100371/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2058)
      previous := (1029)
      next := (1029)
      square := (26990899581367156639943871300000000000000)
      linear := (-1480121165653096592359008720483500000000000)
      constant := (20427886351880341027484847442733463155672716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree056.table
  base := (5557895982286699988972448058202572376009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (13446972)
      previous := (6723486)
      next := (6723486)
      square := (176358537864653001485393255074200000000000000)
      linear := (-9696560258839765025019995772579189000000000000)
      constant := (134173985149221986063445428051652876393668648747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74146539284020204051/20000000000000000000)
  centralHi := (11585396763128156883/3125000000000000000)
  directionLo := (46760976479141224557/12500000000000000000)
  directionHi := (374087811833129796457/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree057.table
  base := (3149215225946093388251777763274896728719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-73821500296907356544308733126091500000000000)
      constant := (1037691778982166243793846141119051027045654319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree057.table
  base := (6295484348448097130761409112105322905263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (960174261707555230309363277626200000000000000)
      linear := (-53735436665867384244611846977084929000000000000)
      constant := (757302733460934523676172925300222660797279736069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46760976479141224557/12500000000000000000)
  centralHi := (374087811833129796457/100000000000000000000)
  directionLo := (377413102222590394913/100000000000000000000)
  directionHi := (188706551111295197457/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree058.table
  base := (3524815094232707688828586315579525616969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-75117063476812980063026038948491500000000000)
      constant := (1075068344577853915735408961818338441006342569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree058.table
  base := (7046926445208797654344262108504056823911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-492106407302464430177033452731148461000000000000)
      constant := (7061200666535547081880911824376884066998565086037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377413102222590394913/100000000000000000000)
  centralHi := (188706551111295197457/50000000000000000000)
  directionLo := (190354674552832960113/50000000000000000000)
  directionHi := (380709349105665920227/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree059.table
  base := (1953628584138298886994159879094880411209/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-76412626656718603581743344770891500000000000)
      constant := (1113095899867069602028596514561649615734625618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree059.table
  base := (3906016876699917967322101072532617307569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-250296942306061201076280141334266280500000000000)
      constant := (3655475994858147136405546563377899281220930843123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190354674552832960113/50000000000000000000)
  centralHi := (380709349105665920227/100000000000000000000)
  directionLo := (191988650226803869481/50000000000000000000)
  directionHi := (383977300453607738963/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree060.table
  base := (8592911458282269740892745239651810123667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-155416379673248454200921301186583000000000000)
      constant := (2303548478077292913977504923224883996106924467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree060.table
  base := (2147659067484536255791466600369429300387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (160029043617925871718227212937700000000000000)
      linear := (-9427432628181118039409020603813271500000000000)
      constant := (140092171058797750040122538142350331439555463254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191988650226803869481/50000000000000000000)
  centralHi := (383977300453607738963/100000000000000000000)
  directionLo := (387217672673679101877/100000000000000000000)
  directionHi := (193608836336839550939/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree061.table
  base := (9384666910002437559355363272912385213937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-158007506033059701238355912831383000000000000)
      constant := (2382206352885764830078436252147550636898662737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree061.table
  base := (4691290344610467790674224155592327726379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-258784419615719173051806971271650380500000000000)
      constant := (3911637603186240007494463486444065094496674543393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387217672673679101877/100000000000000000000)
  centralHi := (193608836336839550939/50000000000000000000)
  directionLo := (195215576221520316077/50000000000000000000)
  directionHi := (78086230488608126431/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree062.table
  base := (5094820598562427868369312274961402665759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-80299316196435474137895262238091500000000000)
      constant := (1231082544616523569838409152131630327800487359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree062.table
  base := (1273466095392268313996574148971459480501/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-263028158270548159039570386240342430500000000000)
      constant := (4042922406440530434328670367266906684261340150268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195215576221520316077/50000000000000000000)
  centralHi := (78086230488608126431/20000000000000000000)
  directionLo := (6150287475123058033/1562500000000000000)
  directionHi := (393618398407875714113/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree063.table
  base := (5503854245059706918453289065268434610491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2058)
      previous := (1029)
      next := (1029)
      square := (26990899581367156639943871300000000000000)
      linear := (-1665201619925328523604338123683500000000000)
      constant := (25953310051045286200158047564946153295914059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree063.table
  base := (5502977911079856220429389164643328618277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (249018)
      previous := (124509)
      next := (124509)
      square := (3265898849345425953433208427300000000000000)
      linear := (-202019574395598749075838096151953500000000000)
      constant := (3156721496139332718013006084061868920377764333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6150287475123058033/1562500000000000000)
  centralHi := (393618398407875714113/100000000000000000000)
  directionLo := (396780042759664912099/100000000000000000000)
  directionHi := (3967800427596649121/1000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree064.table
  base := (11838755285884212241095193431507274225721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-165780885112493442350659747765783000000000000)
      constant := (2625983967672989892909794886021560965415956121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree064.table
  base := (473485977667096902299264966829328611107/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-543031271160412262030194432355453061000000000000)
      constant := (8623795122217161270256261682155671883763506304225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396780042759664912099/100000000000000000000)
  centralHi := (3967800427596649121/1000000000000000000)
  directionLo := (399916692699294383379/100000000000000000000)
  directionHi := (19995834634964719169/5000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree065.table
  base := (12682679200246636305593327940184520851391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-168372011472304689388094359410583000000000000)
      constant := (2709843591420304227800186525060903034564189791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree065.table
  base := (12681208239334946514154117342086612378169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-551518748470070234005721262292837161000000000000)
      constant := (8899174147928525890717493257781967428547386973323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399916692699294383379/100000000000000000000)
  centralHi := (19995834634964719169/5000000000000000000)
  directionLo := (100757232949650505191/25000000000000000000)
  directionHi := (80605786359720404153/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree066.table
  base := (13539387878750499291645686492055662623677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-170963137832115936425528971055383000000000000)
      constant := (2795003034501331747926912114792753645959448477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree066.table
  base := (13538040790480796896294904452597384045029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72030000000000000000000000000000000000000000
      center := (605052)
      previous := (302526)
      next := (302526)
      square := (7935324476921944052143498162200000000000000)
      linear := (-514238958475416167108584106731149000000000000)
      constant := (8428669824405579902953605061853880457276343887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100757232949650505191/25000000000000000000)
  centralHi := (80605786359720404153/20000000000000000000)
  directionLo := (406117321268008144789/100000000000000000000)
  directionHi := (40611732126800814479/10000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree067.table
  base := (1801099751767757026128239675119794002831/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-86777132095963591731481791350091500000000000)
      constant := (1440731048447678105784219092409318501603188924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree067.table
  base := (14407564650142572538273474285691904755481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-568493703089386177956774922167605361000000000000)
      constant := (9462736348060725813159125818659342023009611581227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406117321268008144789/100000000000000000000)
  centralHi := (40611732126800814479/10000000000000000000)
  directionLo := (204591200569014503579/50000000000000000000)
  directionHi := (409182401138029007159/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree068.table
  base := (7645417230051378424958734546475718373033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-88072695275869215250199097172491500000000000)
      constant := (1484610299088033389837898597404760199813652233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree068.table
  base := (7644852735530149452920537771675683797409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-288490590199522074966150876052494730500000000000)
      constant := (4875459146296392640290250988417684777477690622403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204591200569014503579/50000000000000000000)
  centralHi := (409182401138029007159/100000000000000000000)
  directionLo := (103056172840429366871/25000000000000000000)
  directionHi := (82444938272343493497/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree069.table
  base := (16185429431800483558331017898392798435827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-178736516911549677537832805989783000000000000)
      constant := (3058278375592081537756958778634593109044420627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree069.table
  base := (4046099052086059909661316798564540958193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (160029043617925871718227212937700000000000000)
      linear := (-10842012179790780035330158926710621500000000000)
      constant := (185988273082763848462178957330069518382430377106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103056172840429366871/25000000000000000000)
  centralHi := (82444938272343493497/20000000000000000000)
  directionLo := (415244692844404171779/100000000000000000000)
  directionHi := (20762234642220208589/5000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree070.table
  base := (133535326443395308117192901369635124623/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2058)
      previous := (1029)
      next := (1029)
      square := (26990899581367156639943871300000000000000)
      linear := (-1850282074197560454849667526883500000000000)
      constant := (32128931452403086496187648740415175750817728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree070.table
  base := (8545788201124594389238217674959867889339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800415000000000000000000000000000000000000000
      center := (6723486)
      previous := (3361743)
      next := (3361743)
      square := (88179268932326500742696627537100000000000000)
      linear := (-6060776887942449937585259305915894500000000000)
      constant := (105511033014692053304343015961622746781329055137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415244692844404171779/100000000000000000000)
  centralHi := (20762234642220208589/5000000000000000000)
  directionLo := (418242888406514219723/100000000000000000000)
  directionHi := (104560722101628554931/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree071.table
  base := (18012056364343240598078978190459345371077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-183918769631172171612702029279383000000000000)
      constant := (3240291185980082501074961713876660888235955877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree071.table
  base := (720447661255715132079912766817037641603/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-602443612328018065858882241917141761000000000000)
      constant := (10641061331835130058197346466489963699806397985025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418242888406514219723/100000000000000000000)
  centralHi := (104560722101628554931/25000000000000000000)
  directionLo := (421219743684699860757/100000000000000000000)
  directionHi := (210609871842349930379/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree072.table
  base := (4735995854758196015076749105651862359029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-93254947995491709325068320462091500000000000)
      constant := (1666622983536194691169539307544828243048057258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree072.table
  base := (151545539435997511400874269061490560743/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (320058087235851743436454425875400000000000000)
      linear := (-22627077393988001401274410068686143000000000000)
      constant := (405418764814504230442291959583199608399702137875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421219743684699860757/100000000000000000000)
  centralHi := (210609871842349930379/50000000000000000000)
  directionLo := (53021963497006447761/12500000000000000000)
  directionHi := (424175707976051582089/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree073.table
  base := (310754032360739148842400952482988235631/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-94550511175397332843785626284491500000000000)
      constant := (1713749758930489583087494952421864952120000992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree073.table
  base := (4971883689857598612112581459192113185381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-309709283473667004904967950895954980500000000000)
      constant := (5627908421062891518211642874553771083020423969054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53021963497006447761/12500000000000000000)
  centralHi := (424175707976051582089/100000000000000000000)
  directionLo := (106777803757430355779/25000000000000000000)
  directionHi := (427111215029721423117/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree074.table
  base := (20844839839127319323556166456149977491841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-191692148710605912725005864213783000000000000)
      constant := (3523051741150059707485801507509808095957910241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree074.table
  base := (20844178538871470193446271686370474527071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-627906044256991981785462731729294061000000000000)
      constant := (11569591594613690399056661779458865640512138237757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106777803757430355779/25000000000000000000)
  centralHi := (427111215029721423117/100000000000000000000)
  directionLo := (215013341894953854049/50000000000000000000)
  directionHi := (430026683789907708099/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree075.table
  base := (10906846103729335802741559992705816451227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-97141637535208579881220237929291500000000000)
      constant := (1809951274632724671441531164332786665299396027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree075.table
  base := (21813087712610109436822366806016917402637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (960174261707555230309363277626200000000000000)
      linear := (-70710391285183328195665506851853129000000000000)
      constant := (1320847847181759039405177040785620791332194511631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215013341894953854049/50000000000000000000)
  centralHi := (430026683789907708099/100000000000000000000)
  directionLo := (54115314886725575847/12500000000000000000)
  directionHi := (432922519093804606777/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree076.table
  base := (11397391118795002324156968624682422247849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-98437200715114203399937543751691500000000000)
      constant := (1859025931560915161236467792706566495817085449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree076.table
  base := (22794229766819429483565728387155893381497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-644880998876307925736516391604062261000000000000)
      constant := (12209933677151569408932258893329277428129319028299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54115314886725575847/12500000000000000000)
  centralHi := (432922519093804606777/100000000000000000000)
  directionLo := (435799112327808620849/100000000000000000000)
  directionHi := (8715982246556172417/2000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree077.table
  base := (23788080217806017922444100385452747764283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4116)
      previous := (2058)
      next := (2058)
      square := (53981799162734313279887742600000000000000)
      linear := (-4070725056939584772189993860167000000000000)
      constant := (77908155334313759381302874089071184640449867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree077.table
  base := (11893787690613870921393819465798964638349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6615000000000000000000000000000000000000000
      center := (55566)
      previous := (27783)
      next := (27783)
      square := (728754288696913229278484525100000000000000)
      linear := (-55099382373584575620850330708504500000000000)
      constant := (1057218799306015262201720219989464155216535727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435799112327808620849/100000000000000000000)
  centralHi := (8715982246556172417/2000000000000000000)
  directionLo := (109664210511248352241/25000000000000000000)
  directionHi := (87731368408998681793/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree078.table
  base := (24793559347068594757131440519196482317483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-202056654149850900874744310792983000000000000)
      constant := (3918245729694788486389326116052014754044276683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree078.table
  base := (3099137264431377006366564795441071604049/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (160029043617925871718227212937700000000000000)
      linear := (-12256591731400442031251297249607971500000000000)
      constant := (238283906523947522680141495641655538003919678116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109664210511248352241/25000000000000000000)
  centralHi := (87731368408998681793/20000000000000000000)
  directionLo := (441496074546610933851/100000000000000000000)
  directionHi := (110374018636652733463/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree079.table
  base := (25811195449883048653211574057952344600507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-204647780509662147912178922437783000000000000)
      constant := (4020290160016710410304897757469775579385817307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree079.table
  base := (12905387063066559524927805043366813015127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-335171715402640920831548440708107280500000000000)
      constant := (6601212390244999066491091857466440305742128201509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441496074546610933851/100000000000000000000)
  centralHi := (110374018636652733463/25000000000000000000)
  directionLo := (444317164430147780921/100000000000000000000)
  directionHi := (222158582215073890461/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree080.table
  base := (26840966719096155404560099993130575601407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-207238906869473394949613534082583000000000000)
      constant := (4123632849988165090111651067796146512018978207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree080.table
  base := (26840581911867970935657309279079431426189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-678830908114939813638623711353598661000000000000)
      constant := (13541781838102754818978085157987171138428932070663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444317164430147780921/100000000000000000000)
  centralHi := (222158582215073890461/50000000000000000000)
  directionLo := (447120455106258051801/100000000000000000000)
  directionHi := (223560227553129025901/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree081.table
  base := (1115314139355591218336024367971030137309/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-209830033229284641987048145727383000000000000)
      constant := (4228273752379518184748369888720909083991972725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree081.table
  base := (27882502083174948660774813864770236609179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (320058087235851743436454425875400000000000000)
      linear := (-25456236497207325393116686714480843000000000000)
      constant := (514274147149594488160315492134147765659935292259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447120455106258051801/100000000000000000000)
  centralHi := (223560227553129025901/50000000000000000000)
  directionLo := (449906279286706181301/100000000000000000000)
  directionHi := (224953139643353090651/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree082.table
  base := (7234209500125486594530267303897318355313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-106210579794547944512241378686091500000000000)
      constant := (2167106412293998593194874365152842922742213026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree082.table
  base := (14468258577533435484828470617686305194213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-347902931367127878794838685614183430500000000000)
      constant := (7116642524072738136561897752763774807675854784271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449906279286706181301/100000000000000000000)
  centralHi := (224953139643353090651/50000000000000000000)
  directionLo := (56584369930660291643/12500000000000000000)
  directionHi := (90534991889056466629/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree083.table
  base := (30002904263448964230073867851245261301031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-215012285948907136061917369016983000000000000)
      constant := (4441450028184435757906099675680303872383775431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree083.table
  base := (3750326419998947164513306381023691372749/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-352146670021956864782602100582875480500000000000)
      constant := (7292715469870147262022394531620316283235660520732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56584369930660291643/12500000000000000000)
  centralHi := (90534991889056466629/20000000000000000000)
  directionLo := (227713404126748951973/50000000000000000000)
  directionHi := (455426808253497903947/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree084.table
  base := (388512972940504340554042108227349361061/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2058)
      previous := (1029)
      next := (1029)
      square := (26990899581367156639943871300000000000000)
      linear := (-2220442982742024317340326333283500000000000)
      constant := (46428421719432849393498033282989604747679560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree084.table
  base := (6216154095829211203698694502602498424461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (1494108)
      previous := (747054)
      next := (747054)
      square := (19595393096072555720599250563800000000000000)
      linear := (-1616283032547781636146782383453821000000000000)
      constant := (33881722304513066779272135113563492197379439035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227713404126748951973/50000000000000000000)
  centralHi := (455426808253497903947/100000000000000000000)
  directionLo := (229081064496363758301/50000000000000000000)
  directionHi := (458162128992727516603/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree085.table
  base := (32171225692774955292352612996196412232547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-220194538668529630136786592306583000000000000)
      constant := (4659818694279481796911302270768547585770345347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree085.table
  base := (32170981690358613813814203130691686686037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-721268294663229673516257861040519161000000000000)
      constant := (15302510737217406202508012622992053562958282192479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229081064496363758301/50000000000000000000)
  centralHi := (458162128992727516603/100000000000000000000)
  directionLo := (92176243188867060611/20000000000000000000)
  directionHi := (28805075996520956441/6250000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree086.table
  base := (33273456088784277404251720433288547912861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-222785665028340877174221203951383000000000000)
      constant := (4770950097304431732112831079869813803538779261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree086.table
  base := (16636616715455906326647326348697549336581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-364877885986443822745892345488951630500000000000)
      constant := (7833722225911497748234429864978045543981946914927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92176243188867060611/20000000000000000000)
  centralHi := (28805075996520956441/6250000000000000000)
  directionLo := (115896088689801502263/25000000000000000000)
  directionHi := (463584354759206009053/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree087.table
  base := (34387718426848834526767644356398420038341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-225376791388152124211655815596183000000000000)
      constant := (4883379512137265876960533124118808606512056741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree087.table
  base := (34387515273838725934122320015771793110837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (320058087235851743436454425875400000000000000)
      linear := (-27342342566020208054344871145010643000000000000)
      constant := (593949651789526042684629972523852284356353476077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115896088689801502263/25000000000000000000)
  centralHi := (463584354759206009053/100000000000000000000)
  directionLo := (116567955701998596209/25000000000000000000)
  directionHi := (466271822807994384837/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree088.table
  base := (35514003148658078887825576481968386135581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-227967917747963371249090427240983000000000000)
      constant := (4997106915828480606253656788826710095111529981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree088.table
  base := (1109806806761537345943622262504645337181/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 324135000000000000000000000000000000000000000
      center := (2722734)
      previous := (1361367)
      next := (1361367)
      square := (35708960146148748234645741729900000000000000)
      linear := (-3085664159471915658854703929143270500000000000)
      constant := (67810326871669710995894452061747047292374922992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116567955701998596209/25000000000000000000)
  centralHi := (466271822807994384837/100000000000000000000)
  directionLo := (117235972378327115507/25000000000000000000)
  directionHi := (468943889513308462029/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree089.table
  base := (1466092065292576630275933506982322569249/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-230559044107774618286525038885783000000000000)
      constant := (5112132287676899795044206316889325912219171225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree089.table
  base := (9163033144833185034303461305727494742293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-377609101950930780709182590395027780500000000000)
      constant := (8393909949596207436542413797163612422626388051262) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117235972378327115507/25000000000000000000)
  centralHi := (468943889513308462029/100000000000000000000)
  directionLo := (471600816664952771441/100000000000000000000)
  directionHi := (235800408332476385721/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree090.table
  base := (9450651525149865919176383886421495678051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-116575085233792932661979825265291500000000000)
      constant := (2614227804504711054726625743090956022246000902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree090.table
  base := (4725306489555248203162185446624890405027/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (160029043617925871718227212937700000000000000)
      linear := (-14142697800213324692479481680137771500000000000)
      constant := (317959313464523094703082827225675230391435396268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471600816664952771441/100000000000000000000)
  centralHi := (235800408332476385721/50000000000000000000)
  directionLo := (1482008933497736053/312500000000000000)
  directionHi := (474242858719275536961/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree091.table
  base := (19482454769113325130730057902310704312559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2058)
      previous := (1029)
      next := (1029)
      square := (26990899581367156639943871300000000000000)
      linear := (-2405523437014256248585655736483500000000000)
      constant := (54551804724309637644719567136249224511315391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree091.table
  base := (9741192233121539470756517043688630939563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800415000000000000000000000000000000000000000
      center := (6723486)
      previous := (3361743)
      next := (3361743)
      square := (88179268932326500742696627537100000000000000)
      linear := (-7879522025726301075198151435355344500000000000)
      constant := (179143348291153790775589934138483035588396127458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1482008933497736053/312500000000000000)
  centralHi := (474242858719275536961/100000000000000000000)
  directionLo := (238435131541794338993/50000000000000000000)
  directionHi := (476870263083588677987/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree092.table
  base := (40139205617199839845999194687910220628613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-238332423187208359398828873820183000000000000)
      constant := (5464996034402148212499948512484808439729299813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree092.table
  base := (20069538704779762642688548409312373549033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-390340317915417738672472835301103930500000000000)
      constant := (8973277733382609430329077418321240250547642637211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238435131541794338993/50000000000000000000)
  centralHi := (476870263083588677987/100000000000000000000)
  directionLo := (479483270386560432121/100000000000000000000)
  directionHi := (239741635193280216061/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree093.table
  base := (41325488629483923622393565228420824390049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-240923549547019606436263485464983000000000000)
      constant := (5585213109563840983157706259650982399360507649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree093.table
  base := (41325371740535605102016239904606510899073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (960174261707555230309363277626200000000000000)
      linear := (-87685345904499272146719166726621329000000000000)
      constant := (2037924987310890377767379014401931392708728761099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479483270386560432121/100000000000000000000)
  centralHi := (239741635193280216061/50000000000000000000)
  directionLo := (96416422947083400241/20000000000000000000)
  directionHi := (241041057367708500603/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree094.table
  base := (42523753426271089786468671566418834897017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-243514675906830853473698097109783000000000000)
      constant := (5706728076105135245013967712231723622587737817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree094.table
  base := (5315455858634433992246021836706850231173/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4320784177683998536392134749317900000000000000)
      linear := (-398827795225075710647999665238488030500000000000)
      constant := (9370178174984596904123197264792175493539146002364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96416422947083400241/20000000000000000000)
  centralHi := (241041057367708500603/50000000000000000000)
  directionLo := (4846670239607313157/1000000000000000000)
  directionHi := (484667023960731315701/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree095.table
  base := (4373399536319665814213576750984519843409/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-123052901133321050255566354377291500000000000)
      constant := (2914770461437455700458961895309949160720125045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree095.table
  base := (43733898235528400616575721961979593057281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-806143067759809393271526160414360161000000000000)
      constant := (19143649823512554300793819286680968894324047001827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4846670239607313157/1000000000000000000)
  centralHi := (484667023960731315701/100000000000000000000)
  directionLo := (97447643969904668971/20000000000000000000)
  directionHi := (60904777481190418107/12500000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree096.table
  base := (8991242050184331404226543694014198042647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2645108158973981350714499387400000000000000)
      linear := (-248696928626453347548567320399383000000000000)
      constant := (5953651639814566579894077109668208447501977235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree096.table
  base := (449561217281461091892711736359104270291/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (160029043617925871718227212937700000000000000)
      linear := (-15085750834619766023093573895402671500000000000)
      constant := (362059356929171590126096847124831930585460580550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97447643969904668971/20000000000000000000)
  centralHi := (60904777481190418107/12500000000000000000)
  directionLo := (19591836734693877551/4000000000000000000)
  directionHi := (61224489795918367347/12500000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree097.table
  base := (11547598577639103398379606083434991305753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1322554079486990675357249693700000000000000)
      linear := (-125644027493132297293000966022091500000000000)
      constant := (3039530108925493338738869544002242828250225906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree097.table
  base := (46190313639088709664629518080674569347529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8641568355367997072784269498635800000000000000)
      linear := (-823118022379125337222579820289128361000000000000)
      constant := (19963022672872783999615392687025280200408163760443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell068.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19591836734693877551/4000000000000000000)
  centralHi := (61224489795918367347/12500000000000000000)
  directionLo := (492340329869992600287/100000000000000000000)
  directionHi := (15385635308437268759/3125000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree098.table
  base := (189746176533803716143427234852536634749/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (550834685334023604896813700000000000000)
      linear := (-52869467169112003670020104891500000000000)
      constant := (1292329581174511254996634674348567079343625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree098.table
  base := (5929558828093966637743784494158994255723/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (137214)
      previous := (68607)
      next := (68607)
      square := (1799576916986255117197890357900000000000000)
      linear := (-173178987856889485463995553983030500000000000)
      constant := (4243877966134454648759274162148152486933788164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell068.Kernel098
