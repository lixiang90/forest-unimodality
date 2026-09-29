import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell103.Parameters
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch000_049
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch050_099
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch100_149
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch150_199
import ForestUnimodality.BinomialMassData.Q27_52.Batch000_049
import ForestUnimodality.BinomialMassData.Q27_52.Batch050_099
import ForestUnimodality.BinomialMassData.Q27_52.Batch100_149
import ForestUnimodality.BinomialMassData.Q27_52.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree000.table
  base := (184827406678003032083879021/2500000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (361183513137321235419996410000000000000)
      linear := (-15946869143343195187462191000000000000)
      constant := (369654813356006064167758042000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree000.table
  base := (184827406678003032083879021/2500000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (361183513137321235419996410000000000000)
      linear := (-15946869143343195187462191000000000000)
      constant := (369654813356006064167758042000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree001.table
  base := (40886852288982456113949472431864329801103/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-2828541460506115985362944155236322250000000000)
      constant := (1481170278286750565352487620809076785513668267715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree001.table
  base := (3191404579785778734293358310046528401813/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-66082727440824876802890480234000000000000)
      constant := (34536087696547630354283486875154126194009408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9992600812897369001/20000000000000000000)
  directionHi := (24981502032243422503/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree002.table
  base := (24060482240764726875759536482557912795409/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-5541603971101225946296589416127773500000000000)
      constant := (874101671779437127510525823247443686069305803645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree002.table
  base := (240230615486712636275626448654036117185697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-258940867992849507238199700378000000000000)
      constant := (40736222758862302582402257743018103804382793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9992600812897369001/20000000000000000000)
  centralHi := (24981502032243422503/50000000000000000000)
  directionLo := (70658357964899368217/100000000000000000000)
  directionHi := (35329178982449684109/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree003.table
  base := (38026677702151809104473128162194722311411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (59541066)
      previous := (29770533)
      next := (29770533)
      square := (290611505321906901910047891453690000000000000)
      linear := (-917185164632926211914470519668802750000000000)
      constant := (61916743741293134231989598447898603375086686598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree003.table
  base := (151813204823932227069423323729037308164589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-385716281104049260870618440288000000000000)
      constant := (25961043270560262145197565109520055079815541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70658357964899368217/100000000000000000000)
  centralHi := (35329178982449684109/50000000000000000000)
  directionLo := (86538461538461538461/100000000000000000000)
  directionHi := (43269230769230769231/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree004.table
  base := (51677395214151813723861201339078633576689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-10967728992291445868163879937910676000000000000)
      constant := (385717490054252289510030371943435160926555436409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree004.table
  base := (5157060865791774718679917364670212388229/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-256245847107624507251518590099000000000000)
      constant := (8984332995334519916701036958223658936107010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86538461538461538461/100000000000000000000)
  centralHi := (43269230769230769231/50000000000000000000)
  directionLo := (99926008128973690011/100000000000000000000)
  directionHi := (24981502032243422503/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree005.table
  base := (2992776152683952597889146243253751392773/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-27361583005773111658195050397604254500000000000)
      constant := (577580478496499411473396691925560762315355420325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree005.table
  base := (37332661157030153644087099977401588930659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-319633553663224384067727960054000000000000)
      constant := (6727627019807717762459808593247743529281371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99926008128973690011/100000000000000000000)
  centralHi := (24981502032243422503/25000000000000000000)
  directionLo := (111720673448290871687/100000000000000000000)
  directionHi := (13965084181036358961/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree006.table
  base := (56887001659927668757059353484891034813413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-3643078669662592397784704546598573000000000000)
      constant := (51480171977739306636038524413543875192685420517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree006.table
  base := (28386522147356018072968600827722690240843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-383021260218824260883937330009000000000000)
      constant := (5398149526930628402995541494949134650702467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111720673448290871687/100000000000000000000)
  centralHi := (13965084181036358961/12500000000000000000)
  directionLo := (61191932987297381919/50000000000000000000)
  directionHi := (122383865974594763839/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree007.table
  base := (5595653656249038915055354486092612792821/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-19106916524076775750964815720585029750000000000)
      constant := (196977221231715111302611218644236413969843331604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree007.table
  base := (44677528675363732358320253704959264027023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-892817933548848275400293399928000000000000)
      constant := (9182822608976349365148631647982865620566887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61191932987297381919/50000000000000000000)
  centralHi := (122383865974594763839/100000000000000000000)
  directionLo := (132189683508341538651/100000000000000000000)
  directionHi := (33047420877085384663/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree008.table
  base := (36014917740955568410984270444398266036307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-43639958069343771423796921962952962000000000000)
      constant := (351815967631286233361895964054741315934862450667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree008.table
  base := (35944590414456520282115176644127086565811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-1019593346660048029032712139838000000000000)
      constant := (8203447432937263218690080832141477629622059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132189683508341538651/100000000000000000000)
  centralHi := (33047420877085384663/25000000000000000000)
  directionLo := (70658357964899368217/50000000000000000000)
  directionHi := (28263343185959747287/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree009.table
  base := (29355730693642564787752404462803957175519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64580334515979311535566198100820000000000000)
      linear := (-605754112228814707971163117095504500000000000)
      constant := (4044871497596657743948064337860240278573574119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree009.table
  base := (29297376176625404701209088883456165647119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-1146368759771247782665130879748000000000000)
      constant := (7642385312067314175092353553749841994363111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70658357964899368217/50000000000000000000)
  centralHi := (28263343185959747287/20000000000000000000)
  directionLo := (18736126524182566877/12500000000000000000)
  directionHi := (149889012193460535017/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree010.table
  base := (24085851752260855227859646407534959189017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-54492208111724211267531503006518767000000000000)
      constant := (316328123679599122273832919977519185365542014177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree010.table
  base := (1502265223803883889947038740183598250623/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-636572086441223768148774809829000000000000)
      constant := (3690698341988054551867753092393224834842296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18736126524182566877/12500000000000000000)
  centralHi := (149889012193460535017/100000000000000000000)
  directionLo := (78998445794014343287/50000000000000000000)
  directionHi := (6319875663521147463/4000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree011.table
  base := (19798430757400625439756107838534851010733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-59918333132914431189398793528301669500000000000)
      constant := (314950367054882626998228112196472272260178815573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree011.table
  base := (19755615237622987066680640324063504838373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-1399919585993647289929968359568000000000000)
      constant := (7351938969830754959473731890703482317685037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78998445794014343287/50000000000000000000)
  centralHi := (6319875663521147463/4000000000000000000)
  directionLo := (2071356723511308411/1250000000000000000)
  directionHi := (165708537880904672881/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree012.table
  base := (8120903260073415163993201015183599497141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (59541066)
      previous := (29770533)
      next := (29770533)
      square := (290611505321906901910047891453690000000000000)
      linear := (-3630247675228036172848115780560254000000000000)
      constant := (17871051206289671208894189927979920682795122869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree012.table
  base := (16204546395839991820144032610353742052677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-1526694999104847043562387099478000000000000)
      constant := (7511602506700768637850329777415782406902413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2071356723511308411/1250000000000000000)
  centralHi := (165708537880904672881/100000000000000000000)
  directionLo := (173076923076923076923/100000000000000000000)
  directionHi := (43269230769230769231/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree013.table
  base := (13249629590230373713663698115195225495133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (6341652)
      previous := (3170826)
      next := (3170826)
      square := (30952704708842155233022852344180000000000000)
      linear := (-418760847191093911438659021135310500000000000)
      constant := (1984077936515440128360078417866062420365953917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree013.table
  base := (13217082648687693750353317274052681278009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (148)
      previous := (74)
      next := (74)
      square := (722367026274642470839992820000000000000)
      linear := (-9783848592994359746714827452000000000000)
      constant := (46345213016761224463031229713802681278009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173076923076923076923/100000000000000000000)
  centralHi := (43269230769230769231/25000000000000000000)
  directionLo := (11259010814420189073/6250000000000000000)
  directionHi := (180144173030723025169/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree014.table
  base := (10705162399034442629561199035649610734063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-76196708196485090955000665093650377000000000000)
      constant := (354995762843443679413775140361854363350613267303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree014.table
  base := (2669176118945877743142317621666699165051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-890122912663623275413612289649000000000000)
      constant := (4147231325140866755079323598169344317787238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11259010814420189073/6250000000000000000)
  centralHi := (180144173030723025169/100000000000000000000)
  directionLo := (46736110805825915127/25000000000000000000)
  directionHi := (186944443223303660509/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree015.table
  base := (8522444854685592766973189846428954250893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-9069203690852812319651995068381475500000000000)
      constant := (42235135339795241506312279173699098278981765837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree015.table
  base := (8497576069244337108076474897691658874321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-1907021238438446304459643319208000000000000)
      constant := (8883461206515783387566532369298640349760249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46736110805825915127/25000000000000000000)
  centralHi := (186944443223303660509/100000000000000000000)
  directionLo := (9675294133412551571/5000000000000000000)
  directionHi := (193505882668251031421/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree016.table
  base := (6635904825462035944519761258278040874879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-87048958238865530798735246137216182000000000000)
      constant := (410195697569257037720472202323811967712659655799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree016.table
  base := (1653550382423006057224296592290871229317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-1016898325774823029046031029559000000000000)
      constant := (4794133930769944783323847290598314475509146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9675294133412551571/5000000000000000000)
  centralHi := (193505882668251031421/100000000000000000000)
  directionLo := (99926008128973690011/50000000000000000000)
  directionHi := (199852016257947380023/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree017.table
  base := (1248573284277035392073843454254453294681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-46237541630027875360301268329499542250000000000)
      constant := (222431540727552716907987264945613298999202225122) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree017.table
  base := (4975383919703226613259143183841698600829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-2160572064660845811724480799028000000000000)
      constant := (10400230332929506620422621601818997063540101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99926008128973690011/50000000000000000000)
  centralHi := (199852016257947380023/100000000000000000000)
  directionLo := (103001371565521874971/50000000000000000000)
  directionHi := (206002743131043749943/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree018.table
  base := (3556907366481985492287029033002154593813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64580334515979311535566198100820000000000000)
      linear := (-1208656892361061365956417619515827000000000000)
      constant := (5973131159158841454771890629009070685341476013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree018.table
  base := (885115292736653067808614379344324247793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-1143673738886022782678449769469000000000000)
      constant := (5656238365568319721296750194425381595754034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103001371565521874971/50000000000000000000)
  centralHi := (206002743131043749943/100000000000000000000)
  directionLo := (211975073894698104651/100000000000000000000)
  directionHi := (52993768473674526163/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree019.table
  base := (572770811946787321261461417299127510383/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-51663666651218095282168558851282444750000000000)
      constant := (263420393609697747921365579775047061655094094446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree019.table
  base := (2276803279583685003773526795176263665093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-2414122890883245318989318278848000000000000)
      constant := (12319492585512582175520948107185538559400717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211975073894698104651/100000000000000000000)
  centralHi := (52993768473674526163/25000000000000000000)
  directionLo := (10889184281640504371/5000000000000000000)
  directionHi := (217783685632810087421/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree020.table
  base := (1170429371711242255380549183002315213901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-108753458323626410486204408224347792000000000000)
      constant := (573723458548594547579760103726293597327475027381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree020.table
  base := (1158049584895638814326949059310552504277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-2540898303994445072621737018758000000000000)
      constant := (13416822944395856605788115825933483373222813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10889184281640504371/5000000000000000000)
  centralHi := (217783685632810087421/100000000000000000000)
  directionLo := (1787530775172653947/800000000000000000)
  directionHi := (13965084181036358961/6250000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree021.table
  base := (173526670065916528825560506901717196623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-12686620371646292267563522082903410500000000000)
      constant := (69368503567126631943697455278544988724982635407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree021.table
  base := (162809288111774456421425456809309442999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-2667673717105644826254155758668000000000000)
      constant := (14600852762794214560741016038942523295866831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1787530775172653947/800000000000000000)
  centralHi := (13965084181036358961/6250000000000000000)
  directionLo := (228959248072897262639/100000000000000000000)
  directionHi := (2861990600911215783/1250000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree022.table
  base := (-179265565494410679755348931048557476877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-59802854183003425164969494633956798500000000000)
      constant := (339246867625136872389927363739434180938824530326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree022.table
  base := (-45395554981998390143678095865761655021/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-1397224565108422289943287249289000000000000)
      constant := (7934319768128054428625758806537490242411608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228959248072897262639/100000000000000000000)
  centralHi := (2861990600911215783/1250000000000000000)
  directionLo := (58586815418047791061/25000000000000000000)
  directionHi := (46869452334438232849/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree023.table
  base := (-378891331238638156222165300437954563457/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 68445000000000000000000000000000000000000000
      center := (1012986)
      previous := (506493)
      next := (506493)
      square := (4944241111336790391664330856490000000000000)
      linear := (-118177536282794962430818789971357750000000000)
      constant := (695795876101703004594612764765522656524174254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree023.table
  base := (-304713747604145018127079063050423855101/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-2921224543328044333518993238488000000000000)
      constant := (17217782819295314585632163769295141842439655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58586815418047791061/25000000000000000000)
  centralHi := (46869452334438232849/20000000000000000000)
  directionLo := (14975884368241721489/6250000000000000000)
  directionHi := (9584565995674701753/4000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree024.table
  base := (-279201492385253878386599825502103082619/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (59541066)
      previous := (29770533)
      next := (29770533)
      square := (290611505321906901910047891453690000000000000)
      linear := (-7247664356021516120759642795082189000000000000)
      constant := (44289290159698877271554631656457934363188036116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree024.table
  base := (-2240517674246035300798368608501342060759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-3047999956439244087151411978398000000000000)
      constant := (18646320963435898577019438021735273191731729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14975884368241721489/6250000000000000000)
  centralHi := (9584565995674701753/4000000000000000000)
  directionLo := (244767731949189527677/100000000000000000000)
  directionHi := (122383865974594763839/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree025.table
  base := (-2880721341129335654965559814860466377329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-135884083429577510095540860833262304500000000000)
      constant := (861590359755008699629444897598060279530558215751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree025.table
  base := (-577334985182647641337488781133792962913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-3174775369550443840783830718308000000000000)
      constant := (20152648597536079497984295381235694946338515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244767731949189527677/100000000000000000000)
  centralHi := (122383865974594763839/50000000000000000000)
  directionLo := (249815020322434225027/100000000000000000000)
  directionHi := (62453755080608556257/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree026.table
  base := (-3464695315613433016601544764835936638739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (6341652)
      previous := (3170826)
      next := (3170826)
      square := (30952704708842155233022852344180000000000000)
      linear := (-836155079590341597736142907426303000000000000)
      constant := (5498490834807945549937760336495107013466672589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree026.table
  base := (-3469824262924016242717880532806553903859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (148)
      previous := (74)
      next := (74)
      square := (722367026274642470839992820000000000000)
      linear := (-19535803447702033103054730522000000000000)
      constant := (128612131742499840337932290069193446096141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249815020322434225027/100000000000000000000)
  centralHi := (62453755080608556257/25000000000000000000)
  directionLo := (254762332682534043887/100000000000000000000)
  directionHi := (15922645792658377743/6250000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree027.table
  base := (-798387083159423413387262628498379003023/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64580334515979311535566198100820000000000000)
      linear := (-1811559672493308023941672121936149500000000000)
      constant := (12347217779393321918352005628593706171878703885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree027.table
  base := (-249771945238552310619316582192436631377/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-1714163097886421674024334099064000000000000)
      constant := (11696823412581039058292973284828200674378296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254762332682534043887/100000000000000000000)
  centralHi := (15922645792658377743/6250000000000000000)
  directionLo := (32451923076923076923/12500000000000000000)
  directionHi := (51923076923076923077/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree028.table
  base := (-446769995221336889938786835326899594603/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-76081229246574084930571366199305506000000000000)
      constant := (537095674472070424754596039012438913858873364785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree028.table
  base := (-4471499491262824189710244233080665342587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-3555101608884043101681086938038000000000000)
      constant := (25126352046503474873965541454403367557102797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32451923076923076923/12500000000000000000)
  centralHi := (51923076923076923077/20000000000000000000)
  directionLo := (264379367016683077303/100000000000000000000)
  directionHi := (33047420877085384663/12500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree029.table
  base := (-2448156318553853277706559461604260270587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-78794291757169194891505011460196957250000000000)
      constant := (575706883721156367037576473891985013145551880653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree029.table
  base := (-4899580404935708430517204355200972714389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-3681877021995242855313505677948000000000000)
      constant := (26932837362801802829950453661376785611268259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264379367016683077303/100000000000000000000)
  centralHi := (33047420877085384663/12500000000000000000)
  directionLo := (134529505573396370849/50000000000000000000)
  directionHi := (269059011146792741699/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree030.table
  base := (-5281332266357445705407826995405747076073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-18112745392836512189430812604686313000000000000)
      constant := (136862902741405141036246876794847006313367979543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree030.table
  base := (-211365660092251278848803374190102823083/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-3808652435106442608945924417858000000000000)
      constant := (28812503223324498089408249754786815572474325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134529505573396370849/50000000000000000000)
  centralHi := (269059011146792741699/100000000000000000000)
  directionLo := (17103665229276090137/6250000000000000000)
  directionHi := (273658643668417442193/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree031.table
  base := (-5625690909898176217445607103644359058583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-168440833556718829626744603963959719500000000000)
      constant := (1315227188106412210008951321886118517073218318577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree031.table
  base := (-5628105065606440087794039292105100234623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-3935427848217642362578343157768000000000000)
      constant := (30764855762374370350699128529430988060348713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17103665229276090137/6250000000000000000)
  centralHi := (273658643668417442193/100000000000000000000)
  directionLo := (69545558372545348527/25000000000000000000)
  directionHi := (278182233490181394109/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree032.table
  base := (-741475824456634929279235791757998650533/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-86933479288954524774305947242871311000000000000)
      constant := (700889723820173684485285459089145446696558562508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree032.table
  base := (-2966940282630170298259373190270834052607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-2031101630664421058105380948839000000000000)
      constant := (16394743889724868471435912268132229045109417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69545558372545348527/25000000000000000000)
  centralHi := (278182233490181394109/100000000000000000000)
  directionLo := (70658357964899368217/25000000000000000000)
  directionHi := (282633431859597472869/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree033.table
  base := (-3100837650257271489015275290488514629863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (59541066)
      previous := (29770533)
      next := (29770533)
      square := (290611505321906901910047891453690000000000000)
      linear := (-9960726866616626081693288055973640250000000000)
      constant := (82856024969206060122214723457017166271243061433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree033.table
  base := (-6203456516943654754780387768672472148709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-4188978674440041869843180637588000000000000)
      constant := (34886063215401409423428072992172102206868179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70658357964899368217/25000000000000000000)
  centralHi := (282633431859597472869/100000000000000000000)
  directionLo := (35876950857209854137/12500000000000000000)
  directionHi := (287015606857678833097/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree034.table
  base := (-201154566575358255472697081917366033851/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-92359604310144744696173237764654213500000000000)
      constant := (792051125776623126178774340214078573264412026704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree034.table
  base := (-3219237768278159940973271351012174838773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-2157877043775620811737799688749000000000000)
      constant := (18527152234071149192697376502329942452247363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35876950857209854137/12500000000000000000)
  centralHi := (287015606857678833097/100000000000000000000)
  directionLo := (58266374644396603577/20000000000000000000)
  directionHi := (145665936610991508943/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree035.table
  base := (-6638982826561346541744611711994357930799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-190145333641479709314213766051091329500000000000)
      constant := (1679850978456843410863456535304447185015044726681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree035.table
  base := (-3320147865714470988805943861901092157309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-2221264750331220688554009058704000000000000)
      constant := (19646991008766765707420182118963090425414779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58266374644396603577/20000000000000000000)
  centralHi := (145665936610991508943/50000000000000000000)
  directionLo := (147792559124417284373/50000000000000000000)
  directionHi := (295585118248834568747/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree036.table
  base := (-212778566782180484837459126341599800411/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32290167257989655767783099050410000000000000)
      linear := (-1207231226312777340963463312178236000000000000)
      constant := (10979299113264381691495708399699474554895299024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree036.table
  base := (-6810040967359065464571919427665996348971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-4569304913773641130740436857318000000000000)
      constant := (41604905930255323504312467767642446617023901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147792559124417284373/50000000000000000000)
  centralHi := (295585118248834568747/100000000000000000000)
  directionLo := (299778024386921070033/100000000000000000000)
  directionHi := (149889012193460535017/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree037.table
  base := (-6947675111452277515817355044004529404073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-200997583683860149157948347094657134500000000000)
      constant := (1880481914085035800327594506812927275484589047887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree037.table
  base := (-3474321034643198743740334758705693215467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-2348040163442420442186427798614000000000000)
      constant := (21993459448446432073182266117933612846586077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299778024386921070033/100000000000000000000)
  centralHi := (149889012193460535017/50000000000000000000)
  directionLo := (303913089024598236011/100000000000000000000)
  directionHi := (75978272256149559003/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree038.table
  base := (-7056040988692097616231893153449384281157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-206423708705050369079815637616440037000000000000)
      constant := (1985351737787962658996212426492361814328802926483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree038.table
  base := (-7056870624990200920356254284709508426553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-4822855739996040638005274337138000000000000)
      constant := (46439890519111457915287495989308093075912543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303913089024598236011/100000000000000000000)
  centralHi := (75978272256149559003/25000000000000000000)
  directionLo := (307992641885518592619/100000000000000000000)
  directionHi := (15399632094275929631/5000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree039.table
  base := (-3567327516898516272277787040505130895727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (352314)
      previous := (176157)
      next := (176157)
      square := (1719594706046786401834602908010000000000000)
      linear := (-69641628443866071335201488539849750000000000)
      constant := (688116788055880613388155007699405048367943753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree039.table
  base := (-7135366747567618361668352196877963339451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (148)
      previous := (74)
      next := (74)
      square := (722367026274642470839992820000000000000)
      linear := (-29287758302409706459394633592000000000000)
      constant := (289726110164483359242248422289872036660549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307992641885518592619/100000000000000000000)
  centralHi := (15399632094275929631/5000000000000000000)
  directionLo := (62403772075338276227/20000000000000000000)
  directionHi := (19501178773543211321/6250000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree040.table
  base := (-898006428398911276220970805059365005201/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-108637979373715404461775109330002921000000000000)
      constant := (1102088320130860913803168000195935957771088229276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree040.table
  base := (-179616547472622406228260766755591430151/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-2538203283109220072635055908479000000000000)
      constant := (25779147687946388944174209187776100966089620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62403772075338276227/20000000000000000000)
  centralHi := (19501178773543211321/6250000000000000000)
  directionLo := (78998445794014343287/25000000000000000000)
  directionHi := (315993783176057373149/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree041.table
  base := (-7204674103883274841871308572570005015273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-222702083768621028845417509181788744500000000000)
      constant := (2318124636028233069963032643612763556465120860687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree041.table
  base := (-3602598835572702041429907651369589600207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-2601590989664819949451265278434000000000000)
      constant := (27111782082162249499496486494469414357565017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78998445794014343287/25000000000000000000)
  centralHi := (315993783176057373149/100000000000000000000)
  directionLo := (63983864460054329781/20000000000000000000)
  directionHi := (159959661150135824453/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree042.table
  base := (-3598446137108957658635548028841862126797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (59541066)
      previous := (29770533)
      next := (29770533)
      square := (290611505321906901910047891453690000000000000)
      linear := (-12673789377211736042626933316865091500000000000)
      constant := (135282921274212485949556670190661105687269992627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree042.table
  base := (-359867062844935343226691172610309792601/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-2664978696220419826267474648389000000000000)
      constant := (28479728463770917279295090286841576450504310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63983864460054329781/20000000000000000000)
  centralHi := (159959661150135824453/50000000000000000000)
  directionLo := (32379727385543723529/10000000000000000000)
  directionHi := (323797273855437235291/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree043.table
  base := (-7161013222839389491470309337301258956171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-233554333811001468689152090225354549500000000000)
      constant := (2555078255788584453292051233242694401820932870749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree043.table
  base := (-7161398204094955307180509018318167444061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-5456732805552039406167368036688000000000000)
      constant := (59765922027944589096638300020736979701953691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32379727385543723529/10000000000000000000)
  centralHi := (323797273855437235291/100000000000000000000)
  directionLo := (327629327642323477551/100000000000000000000)
  directionHi := (20476832977645217347/6250000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree044.table
  base := (-3548646436510819113570531327824868175227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-119490229416095844305509690373568726000000000000)
      constant := (1339039900661493244005481214257873476656589008813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree044.table
  base := (-7097622941922016162118547975837251291249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-5583508218663239159799786776598000000000000)
      constant := (62642916467000013132164475090365504531778919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327629327642323477551/100000000000000000000)
  centralHi := (20476832977645217347/6250000000000000000)
  directionLo := (2071356723511308411/625000000000000000)
  directionHi := (331417075761809345761/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree045.table
  base := (-350297225725775314226922209292158513501/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32290167257989655767783099050410000000000000)
      linear := (-1508682616378900669956090563388397250000000000)
      constant := (17309232561761435890021091809210664906407470990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree045.table
  base := (-7006227475326615757940153834731821255771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-5710283631774438913432205516508000000000000)
      constant := (65590404415872109915636621699384072207774701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2071356723511308411/625000000000000000)
  centralHi := (331417075761809345761/100000000000000000000)
  directionLo := (335162020344872615063/100000000000000000000)
  directionHi := (41895252543109076883/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree046.table
  base := (-6887146020643691389043544583505906347627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (2025972)
      previous := (1012986)
      next := (1012986)
      square := (9888482222673580783328661712980000000000000)
      linear := (-472273551747773399725432820020233000000000000)
      constant := (5544658957976174119777550437107477210507333997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree046.table
  base := (-6887388573200672178120048101354287738691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-5837059044885638667064624256418000000000000)
      constant := (68608356000618145290947511913219125372161221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335162020344872615063/100000000000000000000)
  centralHi := (41895252543109076883/12500000000000000000)
  directionLo := (338865580513578766931/100000000000000000000)
  directionHi := (84716395128394691733/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree047.table
  base := (-6741045821397058867795659014539549738753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-255258833895762348376621252312486159500000000000)
      constant := (3065165467762158292107646362631661820271390186807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree047.table
  base := (-6741253716455223315938159204886529697327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-5963834457996838420697042996328000000000000)
      constant := (71696746296964153854132837827338926481151737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338865580513578766931/100000000000000000000)
  centralHi := (84716395128394691733/25000000000000000000)
  directionLo := (171264549332277652423/50000000000000000000)
  directionHi := (342529098664555304847/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree048.table
  base := (-6567767851206135590564070896996962681853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-28964995435216952033165393648252118000000000000)
      constant := (355579712723868361807995519671344664853516939523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree048.table
  base := (-656794602416221864085742355343198361211/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-3045304935554019087164730868119000000000000)
      constant := (37427777248893488072426681594386997384776705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171264549332277652423/50000000000000000000)
  centralHi := (342529098664555304847/100000000000000000000)
  directionLo := (173076923076923076923/50000000000000000000)
  directionHi := (346153846153846153847/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree049.table
  base := (-3183707825413420042251106285293439253291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-133055541969071394110177916678025982250000000000)
      constant := (1669139839619475146101667280044194798324201536029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree049.table
  base := (-6367568336764429978249374975705699827263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-6217385284219237927961880476148000000000000)
      constant := (78084763223051783724621298780471486729192553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173076923076923076923/50000000000000000000)
  centralHi := (346153846153846153847/100000000000000000000)
  directionLo := (349741028451407915039/100000000000000000000)
  directionHi := (2185881427821299469/625000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree050.table
  base := (-1535018942682612667540890089979355415711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-135768604479666504071111561938917433500000000000)
      constant := (1739675817590485048448885551740962546761013384018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree050.table
  base := (-6140206603355626349684303273606193455299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-6344160697330437681594299216058000000000000)
      constant := (81384357947361729628791265625910553306054469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349741028451407915039/100000000000000000000)
  centralHi := (2185881427821299469/625000000000000000)
  directionLo := (176645894912248420543/50000000000000000000)
  directionHi := (353291789824496841087/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree051.table
  base := (-5885820597182109701416992558993648382867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-30773703775613692007121157155513085500000000000)
      constant := (402603639795234553448603616507262049521434765997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree051.table
  base := (-1177186538774825448159687960682463973361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-6470936110441637435226717955968000000000000)
      constant := (84754326524697237864290740625880067942509955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176645894912248420543/50000000000000000000)
  centralHi := (353291789824496841087/100000000000000000000)
  directionLo := (356807217601528316811/100000000000000000000)
  directionHi := (89201804400382079203/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree052.table
  base := (-2802355350371435470431345622957795140761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3170826)
      previous := (1585413)
      next := (1585413)
      square := (15476352354421077616511426172090000000000000)
      linear := (-835471772194418485165555340004144000000000000)
      constant := (11155392335937295604912636586460318811013531911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree052.table
  base := (-350300420977862920271077139173870621489/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (361183513137321235419996410000000000000)
      linear := (-19519856578558689907867268331000000000000)
      constant := (260930943176154543529070244933609035028088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356807217601528316811/100000000000000000000)
  centralHi := (89201804400382079203/25000000000000000000)
  directionLo := (360288346061446050337/100000000000000000000)
  directionHi := (180144173030723025169/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree053.table
  base := (-529679678935648523387865356294464230099/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-143907792011451833953912497721591787250000000000)
      constant := (1960310411074721838175674126166436421151854816905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree053.table
  base := (-2648439528088347144771157513214411387631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-3362243468332018471245777717894000000000000)
      constant := (45852673124271102095357218448685639475490361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360288346061446050337/100000000000000000000)
  centralHi := (180144173030723025169/50000000000000000000)
  directionLo := (181868079994016704777/50000000000000000000)
  directionHi := (72747231997606681911/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree054.table
  base := (-4962121333769148993378111965717699445263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64580334515979311535566198100820000000000000)
      linear := (-3620268012890047997897435629197117000000000000)
      constant := (50292927017455834932884993573051059014394042537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree054.table
  base := (-4962191799716064393478273460901795875257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-6851262349775236696123974175698000000000000)
      constant := (95286381767325015914712907032619596497081567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181868079994016704777/50000000000000000000)
  centralHi := (72747231997606681911/20000000000000000000)
  directionLo := (73430319584756858303/20000000000000000000)
  directionHi := (91787899480946072879/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree055.table
  base := (-4600719921198027936970022452825308618397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-298667834065284107751559576486749379500000000000)
      constant := (4229841150636085825679563227182747099523866874043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree055.table
  base := (-920156054661663732879227811436477622209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-6978037762886436449756392915608000000000000)
      constant := (98937759382998167009646729203244926409233395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73430319584756858303/20000000000000000000)
  centralHi := (91787899480946072879/25000000000000000000)
  directionLo := (370535555153801798657/100000000000000000000)
  directionHi := (185267777576900899329/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree056.table
  base := (-421262238344087666591035516671371483041/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-152046979543237163836713433504266141000000000000)
      constant := (2194481396394768314455663405853307511808083881395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree056.table
  base := (-526584258544340192837794126168684830887/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-3552406587998818101694405827759000000000000)
      constant := (51329737047307421892543607423723969054320388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370535555153801798657/100000000000000000000)
  centralHi := (185267777576900899329/50000000000000000000)
  directionLo := (373888886446607321017/100000000000000000000)
  directionHi := (186944443223303660509/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree057.table
  base := (-3797853737620795997429112815868573973691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-34391120456407171955032684170035020500000000000)
      constant := (505676870412583714447768855082810237391727458181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree057.table
  base := (-3797897995730778034842212887105176541963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-7231588589108835957021230395428000000000000)
      constant := (106451521709137085894945108675948975164408253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373888886446607321017/100000000000000000000)
  centralHi := (186944443223303660509/50000000000000000000)
  directionLo := (377212408575635211251/100000000000000000000)
  directionHi := (94303102143908802813/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree058.table
  base := (-839108742793657241189853021992724713619/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-157473104564427383758580724026049043500000000000)
      constant := (2358114060713555545755100948117076724977445140522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree058.table
  base := (-3356472865939596845658877244371445860177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-7358364002220035710653649135338000000000000)
      constant := (110313898709589867968101916893135225649630087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377212408575635211251/100000000000000000000)
  centralHi := (94303102143908802813/25000000000000000000)
  directionLo := (380506902642488053007/100000000000000000000)
  directionHi := (23781681415155503313/6250000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree059.table
  base := (-722095924316493506079437167702284011771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-160186167075022493719514369286940494750000000000)
      constant := (2442185764192860032619202015781748498008375554298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree059.table
  base := (-144420807018578115643513256645958697247/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-3742569707665617732143033937624000000000000)
      constant := (57123301072499107525741655589628704801652570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380506902642488053007/100000000000000000000)
  centralHi := (23781681415155503313/6250000000000000000)
  directionLo := (95943279055168779267/25000000000000000000)
  directionHi := (383773116220675117069/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree060.table
  base := (-598428675581611362481418385127835899541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (59541066)
      previous := (29770533)
      next := (29770533)
      square := (290611505321906901910047891453690000000000000)
      linear := (-18099914398401955964494223838647994000000000000)
      constant := (280862330417412042147295474608286666044412431062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree060.table
  base := (-1196871237639248698984707514240609301857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-3805957414221217608959243307579000000000000)
      constant := (59124814769227784532298484015958337027986167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95943279055168779267/25000000000000000000)
  centralHi := (383773116220675117069/100000000000000000000)
  directionLo := (9675294133412551571/2500000000000000000)
  directionHi := (387011765336502062841/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree061.table
  base := (-1872440403731869905164892396445553296267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-331224584192425427282763319617446794500000000000)
      constant := (5229679288890010053105325116621577114098720148573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree061.table
  base := (-1872464176386745502907311241577743490559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-7738690241553634971550905355068000000000000)
      constant := (122322978810294177972513171102635111350095529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9675294133412551571/2500000000000000000)
  centralHi := (387011765336502062841/100000000000000000000)
  directionLo := (15608941452079249497/4000000000000000000)
  directionHi := (195111768150990618713/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree062.table
  base := (-264914246512954327829115241442707387103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-336650709213615647204630610139229697000000000000)
      constant := (5406843476979014039818453182604867044901169902285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree062.table
  base := (-1324591579029677068469843169255934582793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-7865465654664834725183324094978000000000000)
      constant := (126466648213842702170739105083311747055507983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15608941452079249497/4000000000000000000)
  centralHi := (195111768150990618713/50000000000000000000)
  directionLo := (49176135926631691921/12500000000000000000)
  directionHi := (393409087413053535369/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree063.table
  base := (-4688224711794783308622913464525816729/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32290167257989655767783099050410000000000000)
      linear := (-2111585396511147327941345065808719750000000000)
      constant := (34487743508076535035072709207160592548251353680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree063.table
  base := (-750133366162660380402682661752215884253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-7992241067776034478815742834888000000000000)
      constant := (130680636281681684418983751431256625515561243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49176135926631691921/12500000000000000000)
  centralHi := (393409087413053535369/100000000000000000000)
  directionLo := (198284525262512307977/50000000000000000000)
  directionHi := (79313810105004923191/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree064.table
  base := (-74540967427638336726970475796859840971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-173751479627998043524182595591397751000000000000)
      constant := (2885096074764521064137257919789859083601945481949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree064.table
  base := (-37274208634913943485284728491338030263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-4059508240443617116224080787399000000000000)
      constant := (67482470890329852710296171446265927745771106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198284525262512307977/50000000000000000000)
  centralHi := (79313810105004923191/20000000000000000000)
  directionLo := (99926008128973690011/25000000000000000000)
  directionHi := (79940806503178952009/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree065.table
  base := (478524630725976997802197236264733767277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (6341652)
      previous := (3170826)
      next := (3170826)
      square := (30952704708842155233022852344180000000000000)
      linear := (-2088337776788084656628594566299280500000000000)
      constant := (35244831572713750124490486370691395155319052173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree065.table
  base := (478511882395848124351567186824615640269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (148)
      previous := (74)
      next := (74)
      square := (722367026274642470839992820000000000000)
      linear := (-48791668011825053172074439732000000000000)
      constant := (824376116415531453240684586610574615640269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99926008128973690011/25000000000000000000)
  centralHi := (79940806503178952009/20000000000000000000)
  directionLo := (80562923329436199057/20000000000000000000)
  directionHi := (201407308323590497643/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree066.table
  base := (1132698534248743941065241758163201530427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-39817245477597391876899974691817923000000000000)
      constant := (682840841041012089902757101388241249982695338043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree066.table
  base := (1132687627784336015610489008913928605373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-8372567307109633739712999054618000000000000)
      constant := (143744501090867756864725632184464453934308037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80562923329436199057/20000000000000000000)
  centralHi := (201407308323590497643/50000000000000000000)
  directionLo := (101475340957718427863/25000000000000000000)
  directionHi := (405901363830873711453/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree067.table
  base := (1813435394581585982101816852127112592489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-363781334319566746813967062748144209500000000000)
      constant := (6337765218544617174490895306975495194501494836209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree067.table
  base := (1813426064854887920252798380022001001189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-8499342720220833493345417794528000000000000)
      constant := (148239753297674243745192656073248468169200941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101475340957718427863/25000000000000000000)
  centralHi := (405901363830873711453/100000000000000000000)
  directionLo := (204482406905160940427/50000000000000000000)
  directionHi := (81792962762064376171/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree068.table
  base := (630182881451748814111283859618829023551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-184603729670378483367917176634963556000000000000)
      constant := (3266484728311823633184624783161130537607586238062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree068.table
  base := (630180886428534124217966270980203418149/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-4313059066666016623488918267219000000000000)
      constant := (76402659839075148579189523148498308755334362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204482406905160940427/50000000000000000000)
  centralHi := (81792962762064376171/20000000000000000000)
  directionLo := (103001371565521874971/25000000000000000000)
  directionHi := (82401097252417499977/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree069.table
  base := (130183353050624633883518471505565501127/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15210000000000000000000000000000000000000000
      center := (225108)
      previous := (112554)
      next := (112554)
      square := (1098720246963731198147629079220000000000000)
      linear := (-78688003436661874954358673344194500000000000)
      constant := (1413816479971768912080367825275420331305354175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree069.table
  base := (1627288500646348034923279075949168216369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-4376446773221616500305127637174000000000000)
      constant := (78720599856811595462552415860998284428566361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103001371565521874971/25000000000000000000)
  centralHi := (82401097252417499977/20000000000000000000)
  directionLo := (415023881825139191099/100000000000000000000)
  directionHi := (4150238818251391911/1000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree070.table
  base := (4014989685441128230830000537583641914537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-380059709383137406579568934313492917000000000000)
      constant := (6932397613206446418609856258358976457897423309297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree070.table
  base := (4014983849004150442708441411258631642903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-8879668959554432754242674014258000000000000)
      constant := (162147392967635820708166846635062708747650607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415023881825139191099/100000000000000000000)
  centralHi := (4150238818251391911/1000000000000000000)
  directionLo := (209010241531578440967/50000000000000000000)
  directionHi := (83604096612631376387/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree071.table
  base := (4801946905790338980108758391683795629017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-385485834404327626501436224835275819500000000000)
      constant := (7136621496892743869069906021470224311758534654177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree071.table
  base := (192077676609571495916313922688228821579/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-9006444372665632507875092754168000000000000)
      constant := (166923899072848229642799197347874516771171275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209010241531578440967/50000000000000000000)
  centralHi := (83604096612631376387/20000000000000000000)
  directionLo := (52624469420648164173/12500000000000000000)
  directionHi := (84199151073037062677/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree072.table
  base := (2807726818549166213073243878062738303293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32290167257989655767783099050410000000000000)
      linear := (-2413036786577270656933972317018881000000000000)
      constant := (45332419128433259160881013290411228867052697493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree072.table
  base := (5615449370291017963156801163551964647327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-9133219785776832261507511494078000000000000)
      constant := (171770717720039919692685215754836282025398263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52624469420648164173/12500000000000000000)
  centralHi := (84199151073037062677/20000000000000000000)
  directionLo := (423950147789396209303/100000000000000000000)
  directionHi := (52993768473674526163/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree073.table
  base := (806938540166844371304211357897875488977/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-198169042223354033172585402939420812250000000000)
      constant := (3777044403832165780290711248341816410151733119748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree073.table
  base := (645550467369942952719957574885618930847/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-4629997599444016007569965116994000000000000)
      constant := (88343924324436582813261342169577222996565715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423950147789396209303/100000000000000000000)
  centralHi := (52993768473674526163/12500000000000000000)
  directionLo := (213442046927145318131/50000000000000000000)
  directionHi := (426884093854290636263/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree074.table
  base := (114407963223715486520275074892879650957/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-200882104733949143133519048200312263500000000000)
      constant := (3883666106982517456656705388740332995667385914144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree074.table
  base := (3661053264167508950027847367311139716087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-4693385305999615884386174486949000000000000)
      constant := (90837645820066540618102451236436582612018703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213442046927145318131/50000000000000000000)
  centralHi := (426884093854290636263/100000000000000000000)
  directionLo := (429798012281288645749/100000000000000000000)
  directionHi := (1719192049125154583/400000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree075.table
  base := (4107628253384112789728014729917465074227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (59541066)
      previous := (29770533)
      next := (29770533)
      square := (290611505321906901910047891453690000000000000)
      linear := (-22621685249393805899383632606800412750000000000)
      constant := (443532339428024422479246474548638228257471212243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree075.table
  base := (1643050768362470633957304347839876027393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-9513546025110431522404767713808000000000000)
      constant := (186733046509206528866614240607493445243147085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429798012281288645749/100000000000000000000)
  centralHi := (1719192049125154583/400000000000000000)
  directionLo := (432692307692307692307/100000000000000000000)
  directionHi := (108173076923076923077/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree076.table
  base := (9134947971566341126980149423644252014269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-412616459510278726110772677444190332000000000000)
      constant := (8202838488139859893909086501509652007470540692389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree076.table
  base := (73079565552443153893832393961219280859/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-9640321438221631276037186453718000000000000)
      constant := (191861113100600657571907650472568757308146375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432692307692307692307/100000000000000000000)
  centralHi := (108173076923076923077/25000000000000000000)
  directionLo := (10889184281640504371/2500000000000000000)
  directionHi := (435567371265620174841/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree077.table
  base := (10081183256216887166735093471483460256507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-418042584531468946032639967965973234500000000000)
      constant := (8425101343590388329256106136056128169589875566867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree077.table
  base := (10081181310026952468004822363678367710143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-9767096851332831029669605193628000000000000)
      constant := (197059491283334182473128673191891394143014167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10889184281640504371/2500000000000000000)
  centralHi := (435567371265620174841/100000000000000000000)
  directionLo := (438423581352999912451/100000000000000000000)
  directionHi := (109605895338249978113/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree078.table
  base := (552698084984413940533098326711473189897/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (352314)
      previous := (176157)
      next := (176157)
      square := (1719594706046786401834602908010000000000000)
      linear := (-139207333843740685718115469588348500000000000)
      constant := (2843645848543450771959477261666952019820996170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree078.table
  base := (11053960036794701879387117927308984969037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (148)
      previous := (74)
      next := (74)
      square := (722367026274642470839992820000000000000)
      linear := (-58543622866532726528414342802000000000000)
      constant := (1197208171284387813484869778403308984969037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438423581352999912451/100000000000000000000)
  centralHi := (109605895338249978113/25000000000000000000)
  directionLo := (441261304060914071829/100000000000000000000)
  directionHi := (44126130406091407183/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree079.table
  base := (12053282744926799398974554413554185495813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-428894834573849385876374549009539039500000000000)
      constant := (8878646467142332745871732249134748629191530419053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree079.table
  base := (12053281324239861664774817456014405692737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-10020647677555230536934442673448000000000000)
      constant := (207667181998812657633119519524247184562072553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441261304060914071829/100000000000000000000)
  centralHi := (44126130406091407183/10000000000000000000)
  directionLo := (111020223449572012687/25000000000000000000)
  directionHi := (444080893798288050749/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree080.table
  base := (2615829184491847135479505228648553280017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-434320959595039605798241839531321942000000000000)
      constant := (9109928727810173468179330415527213381273653925885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree080.table
  base := (6539572354413287501838262088042084473053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-5073711545333215145283430706679000000000000)
      constant := (106538247180124987066497604029699112275945957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111020223449572012687/25000000000000000000)
  centralHi := (444080893798288050749/100000000000000000000)
  directionLo := (446882693793163486751/100000000000000000000)
  directionHi := (13965084181036358961/3125000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree081.table
  base := (14131550836591702207995756315455814805749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64580334515979311535566198100820000000000000)
      linear := (-5428976353286787971853199136458084500000000000)
      constant := (115360709264287526691463462213515754252573766349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree081.table
  base := (7065774899971841977147822213408971249131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-5137099251888815022099640076634000000000000)
      constant := (109278058982680102143203216913476991141103139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446882693793163486751/100000000000000000000)
  centralHi := (13965084181036358961/3125000000000000000)
  directionLo := (8993340731607632101/2000000000000000000)
  directionHi := (449667036580381605051/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree082.table
  base := (7605248576895713659474321833090868895613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-222586604818710022820988210287443873500000000000)
      constant := (4790756316259205049210267600487760417412322522853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree082.table
  base := (95065601677556605101239015888147246121/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-5200486958444414898915849446589000000000000)
      constant := (112053026379255783917989930849670750767555920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8993340731607632101/2000000000000000000)
  centralHi := (449667036580381605051/100000000000000000000)
  directionLo := (113108561115563379333/25000000000000000000)
  directionHi := (452434244462253517333/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree083.table
  base := (16315984592904491207254858675823146804521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-450599334658610265563843711096670649500000000000)
      constant := (9821814272107564009086356829878543985523274535601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree083.table
  base := (8157991918396181316058781936949071757347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-5263874665000014775732058816544000000000000)
      constant := (114863149346409169424968705070520768126991643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113108561115563379333/25000000000000000000)
  centralHi := (452434244462253517333/100000000000000000000)
  directionLo := (455184629944024039767/100000000000000000000)
  directionHi := (56898078743003004971/12500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree084.table
  base := (8724006458459011617434209390292823206197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (59541066)
      previous := (29770533)
      next := (29770533)
      square := (290611505321906901910047891453690000000000000)
      linear := (-25334747759988915860317277867691864000000000000)
      constant := (559173464858801510806952081452322063562114961973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree084.table
  base := (17448012271267291859208441646399349453853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-10654524743111229305096536372998000000000000)
      constant := (235416855728763871015538245966943490057701157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455184629944024039767/100000000000000000000)
  centralHi := (56898078743003004971/12500000000000000000)
  directionLo := (457918496145794525279/100000000000000000000)
  directionHi := (2861990600911215783/625000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree085.table
  base := (9303290963010963927690507209795446023313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-230725792350495352703789146070118227250000000000)
      constant := (5155718458562039322114688358919030717553409146553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree085.table
  base := (18606581374750430919150259258425528486557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-10781300156222429058728955112908000000000000)
      constant := (241177723833041067438046184971447664314228133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457918496145794525279/100000000000000000000)
  centralHi := (2861990600911215783/625000000000000000)
  directionLo := (11515903429811042307/2500000000000000000)
  directionHi := (460636137192441692281/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree086.table
  base := (19791691451764275715642704044176753567647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-466877709722180925329445582662019357000000000000)
      constant := (10560757919884676912374896993091589467664297965207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree086.table
  base := (4947922745280690455720272417544022028977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-5454037784666814406180686926409000000000000)
      constant := (123504451488787907038654880742413879445794226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11515903429811042307/2500000000000000000)
  centralHi := (460636137192441692281/100000000000000000000)
  directionLo := (463337838582952227129/100000000000000000000)
  directionHi := (46333783858295222713/10000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree087.table
  base := (10501670676063643233350492051495084894421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (59541066)
      previous := (29770533)
      next := (29770533)
      square := (290611505321906901910047891453690000000000000)
      linear := (-26239101930187285847295159621322347750000000000)
      constant := (600726965261766830050143631529601418050877686389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree087.table
  base := (1050167047518114372297879173807799020573/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-5517425491222414282996896296364000000000000)
      constant := (126455196569352196709649024728777555344768370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463337838582952227129/100000000000000000000)
  centralHi := (46333783858295222713/10000000000000000000)
  directionLo := (466023877540485925781/100000000000000000000)
  directionHi := (233011938770242962891/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree088.table
  base := (11120765753689180273215185853320284285709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-238864979882280682586590081852792581000000000000)
      constant := (5534209640369207692501350918601211338569560295029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree088.table
  base := (22241531164443590075845394205610960444757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-11161626395556028319626211332638000000000000)
      constant := (258882194296480509870592744336072252315163933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466023877540485925781/100000000000000000000)
  centralHi := (233011938770242962891/50000000000000000000)
  directionLo := (58586815418047791061/12500000000000000000)
  directionHi := (468694523344382328489/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree089.table
  base := (5876565454143434901104033752917238299627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-241578042392875792547523727113684032250000000000)
      constant := (5663379818616765968256063389667938812665004955174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree089.table
  base := (5876565380970765320267672725143387528123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-5644200904333614036629315036274000000000000)
      constant := (132462153217045716803137384344241339984505574) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58586815418047791061/12500000000000000000)
  centralHi := (468694523344382328489/100000000000000000000)
  directionLo := (942700075290472607/200000000000000000)
  directionHi := (471350037645236303501/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree090.table
  base := (24797532194611801099614408400978794453483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64580334515979311535566198100820000000000000)
      linear := (-6031879133419034629838453638878407000000000000)
      constant := (143063042513344331021366905196301636765435833683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree090.table
  base := (24797531944827802250210948957860421147943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-11415177221778427826891048812458000000000000)
      constant := (271036729537366024727213715856848411174002367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (942700075290472607/200000000000000000)
  centralHi := (471350037645236303501/100000000000000000000)
  directionLo := (236995337382043029861/50000000000000000000)
  directionHi := (473990674764086059723/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree091.table
  base := (1632208910609332348270132236443715940071/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3170826)
      previous := (1585413)
      next := (1585413)
      square := (15476352354421077616511426172090000000000000)
      linear := (-1461563120793290014611781169440632750000000000)
      constant := (35066448814381552648314678611651327376091318232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree091.table
  base := (5223068471320475464825160739031007518301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (148)
      previous := (74)
      next := (74)
      square := (722367026274642470839992820000000000000)
      linear := (-68295577721240399884754245872000000000000)
      constant := (1640351855587929790574052450945905037591505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236995337382043029861/50000000000000000000)
  centralHi := (473990674764086059723/100000000000000000000)
  directionLo := (476616681976681905629/100000000000000000000)
  directionHi := (47661668197668190563/10000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree092.table
  base := (5491938576301546780070436125456647759051/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (2025972)
      previous := (1012986)
      next := (1012986)
      square := (9888482222673580783328661712980000000000000)
      linear := (-944110510112140349453023300175268000000000000)
      constant := (22910811727477881996004314812298810005868245695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree092.table
  base := (1098387707985648196682972996422086961713/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-11668728048000827334155886292278000000000000)
      constant := (283472508595007179957687996543389317413237425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476616681976681905629/100000000000000000000)
  centralHi := (47661668197668190563/10000000000000000000)
  directionLo := (479228299783735087649/100000000000000000000)
  directionHi := (9584565995674701753/2000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree093.table
  base := (28830583078908054252568320486973408397529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-56095620541168051642501846257166630500000000000)
      constant := (1376687284104025747254247802006313774360452411161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree093.table
  base := (5766116584749160861926760906989592391159/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-11795503461112027087788305032188000000000000)
      constant := (289795864530823617537650675193763955570529355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479228299783735087649/100000000000000000000)
  centralHi := (9584565995674701753/2000000000000000000)
  directionLo := (481825762167982666337/100000000000000000000)
  directionHi := (240912881083991333169/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree094.table
  base := (3022801311898263453719844139627362385481/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-255143354945851342352191953418141288500000000000)
      constant := (6331779079125555932515437271503078043754126686805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree094.table
  base := (60456025973231463093603789941379625003/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-5961139437111613420710361886049000000000000)
      constant := (148094765697330336159253751708489289156376750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481825762167982666337/100000000000000000000)
  centralHi := (240912881083991333169/50000000000000000000)
  directionLo := (242204648419423055797/50000000000000000000)
  directionHi := (96881859367769222319/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree095.table
  base := (31651982965520339405601425494734379205631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-515712834912892904626251197358065479500000000000)
      constant := (12939937207518217746498602479748861099017496979511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree095.table
  base := (7912995713152531073261542064029623764663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-6024527143667213297526571256004000000000000)
      constant := (151326754590247519282776750443756387832456094) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242204648419423055797/50000000000000000000)
  centralHi := (96881859367769222319/20000000000000000000)
  directionLo := (60872390683175957391/12500000000000000000)
  directionHi := (486979125465407659129/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree096.table
  base := (33102492588008391468150615977657207248393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-57904328881564791616457609764427598000000000000)
      constant := (1468813633835176852440800332882243815866922243337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree096.table
  base := (16551246245851789169392840339326569041947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-6087914850222813174342780625959000000000000)
      constant := (154593898941626211483684744058970190168089043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60872390683175957391/12500000000000000000)
  centralHi := (486979125465407659129/100000000000000000000)
  directionLo := (244767731949189527677/50000000000000000000)
  directionHi := (97907092779675811071/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree097.table
  base := (2161221372546251301975828809975319974763/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-263282542477636672234992889200815642250000000000)
      constant := (6750857324530039277841729545112024845380896452024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree097.table
  base := (1728977093930290125032312357630847309107/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-6151302556778413051158989995914000000000000)
      constant := (157896198749329383156982613914391006952390830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244767731949189527677/50000000000000000000)
  centralHi := (97907092779675811071/20000000000000000000)
  directionLo := (492078522381691753943/100000000000000000000)
  directionHi := (61509815297711469243/12500000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree098.table
  base := (18041565531030944356534484914228026627189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-265995604988231782195926534461707093500000000000)
      constant := (6893556520495938078132144814735083427019533226909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree098.table
  base := (9020782748004828980515237780971489741687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-6214690263334012927975199365869000000000000)
      constant := (161233654011557397170290455561195363532690206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492078522381691753943/100000000000000000000)
  centralHi := (61509815297711469243/12500000000000000000)
  directionLo := (6182606321928694719/1250000000000000000)
  directionHi := (494608505754295577521/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree099.table
  base := (18806629936869677627445324932191785276873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32290167257989655767783099050410000000000000)
      linear := (-3317390956775640643911854070649364750000000000)
      constant := (86885912840616905405178057510263483709600223073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree099.table
  base := (37613259814013506654654365424885421803507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-12556155939779225609582817471648000000000000)
      constant := (329212529453590233627941090807446386284792683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6182606321928694719/1250000000000000000)
  centralHi := (494608505754295577521/100000000000000000000)
  directionLo := (6214070170533925233/1250000000000000000)
  directionHi := (497125613642714018641/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree100.table
  base := (306015065472039929560373323228961303041/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-271421730009422002117793824983489996000000000000)
      constant := (7183464583256549948965369193031357777620225198144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree100.table
  base := (19584964164748392066387421094571431846511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-6341465676445212681607618105779000000000000)
      constant := (168014030893767302685225319197257571982060359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6214070170533925233/1250000000000000000)
  centralHi := (497125613642714018641/100000000000000000000)
  directionLo := (99926008128973690011/20000000000000000000)
  directionHi := (62453755080608556257/12500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree101.table
  base := (8150627313837519261341003525408847537643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-548269585040034224157454940488762894500000000000)
      constant := (14661346899897803077819794192071944550456817846415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree101.table
  base := (2547071032860714536745166770265713010367/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-6404853383000812558423827475734000000000000)
      constant := (171456952511400997801616551185490118990016184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99926008128973690011/20000000000000000000)
  centralHi := (62453755080608556257/12500000000000000000)
  directionLo := (502121976505650296559/100000000000000000000)
  directionHi := (6276524706320628707/1250000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree102.table
  base := (42362884429170080310380891923772779769517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-61521745562358271564369136778949533000000000000)
      constant := (1662085675583926945211357088428307115120071303853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree102.table
  base := (42362884392158193156999001383918343215071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-12936482179112824870480073691378000000000000)
      constant := (349870059157587609578424778363418200003346999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502121976505650296559/100000000000000000000)
  centralHi := (6276524706320628707/1250000000000000000)
  directionLo := (20184064251387578553/4000000000000000000)
  directionHi := (252300803142344731913/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree103.table
  base := (43999171951229331456750348812936927203863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-559121835082414664001189521532328699500000000000)
      constant := (15259201707519536613640932781496104139248282041103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree103.table
  base := (43999171919679641334647469579470845334139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-13063257592224024624112492431288000000000000)
      constant := (356896524190374262554620439539543322861469491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20184064251387578553/4000000000000000000)
  centralHi := (252300803142344731913/50000000000000000000)
  directionLo := (507069110516738819017/100000000000000000000)
  directionHi := (253534555258369409509/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree104.table
  base := (22830999563842274771452815885776149819759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3170826)
      previous := (1585413)
      next := (1585413)
      square := (15476352354421077616511426172090000000000000)
      linear := (-1670260236992913857760523112586129000000000000)
      constant := (46043310004836582926928397885745998243626853391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree104.table
  base := (45661999100793143962190392184144348348343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (148)
      previous := (74)
      next := (74)
      square := (722367026274642470839992820000000000000)
      linear := (-78047532575948073241094148942000000000000)
      constant := (2153806509585131654011855371932144348348343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507069110516738819017/100000000000000000000)
  centralHi := (253534555258369409509/50000000000000000000)
  directionLo := (254762332682534043887/50000000000000000000)
  directionHi := (20380986614602723511/4000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree105.table
  base := (23675682976042345898884422752199051396721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (59541066)
      previous := (29770533)
      next := (29770533)
      square := (290611505321906901910047891453690000000000000)
      linear := (-31665226951377505769162450143105250250000000000)
      constant := (881615683475239591679325721067364614709326787089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree105.table
  base := (47351365929165626969314806925298375300581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-13316808418446424131377329911108000000000000)
      constant := (371160386945056280980691242690309175425798189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254762332682534043887/50000000000000000000)
  centralHi := (20380986614602723511/4000000000000000000)
  directionLo := (511968442768236003683/100000000000000000000)
  directionHi := (127992110692059000921/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree106.table
  base := (49067272419015559376771492437911859767097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-575400210145985323766791393097677407000000000000)
      constant := (16178532270238972658355961534609852335740597350657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree106.table
  base := (1226681809987090108628029911424022139361/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-6721791915778811942504874325509000000000000)
      constant := (189198892332491688888420737804702194831040180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511968442768236003683/100000000000000000000)
  centralHi := (127992110692059000921/25000000000000000000)
  directionLo := (257200305290293382931/50000000000000000000)
  directionHi := (514400610580586765863/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree107.table
  base := (10161943704787410017259680606174534874679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-580826335167175543688658683619460309500000000000)
      constant := (16490988684655867989912971580029485382722251797995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree107.table
  base := (50809718507292946279813542719981296739817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-13570359244668823638642167390928000000000000)
      constant := (385705493278915791978598729561821589149029073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257200305290293382931/50000000000000000000)
  centralHi := (514400610580586765863/100000000000000000000)
  directionLo := (258410666353397844009/50000000000000000000)
  directionHi := (516821332706795688019/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree108.table
  base := (52578704263045859475337573490492482962921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64580334515979311535566198100820000000000000)
      linear := (-7237684693683527945808962643719052000000000000)
      constant := (207487056120709346765181163694247648219368100321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree108.table
  base := (52578704248863730350542539614830104347559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-13697134657780023392274586130838000000000000)
      constant := (393083512786223166696501471816740287634737471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258410666353397844009/50000000000000000000)
  centralHi := (516821332706795688019/100000000000000000000)
  directionLo := (519230769230769230769/100000000000000000000)
  directionHi := (51923076923076923077/10000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree109.table
  base := (54374229633159651187969028365478870731001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-591678585209555983532393264663026114500000000000)
      constant := (17124920853580695124299065832472574257628124852481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree109.table
  base := (54374229621076249493601422679788535331869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-13823910070891223145907004870748000000000000)
      constant := (400531843186378271436783259180130012471085861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519230769230769230769/100000000000000000000)
  centralHi := (51923076923076923077/10000000000000000000)
  directionLo := (130407269134796570481/25000000000000000000)
  directionHi := (20865163061567451277/4000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree110.table
  base := (56196294631619340326946534006545310854521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-597104710230746203454260555184809017000000000000)
      constant := (17446396608046326386110350746452160590754607585601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree110.table
  base := (5619629462132486574824601992109925277/1000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-6975342742001211449769711805329000000000000)
      constant := (204025242239470376692039163292522886859065000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130407269134796570481/25000000000000000000)
  centralHi := (20865163061567451277/4000000000000000000)
  directionLo := (524016407439950480553/100000000000000000000)
  directionHi := (262008203719975240277/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree111.table
  base := (58044899256206658765594242389392740859537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-66947870583548491486236427300732435500000000000)
      constant := (1974542089906476369657922250505107700658376206033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree111.table
  base := (58044899247436917422959561448257135019459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-14077460897113622653171842350568000000000000)
      constant := (415639436663543432712520339919992205818288571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524016407439950480553/100000000000000000000)
  centralHi := (262008203719975240277/50000000000000000000)
  directionLo := (263196455637903736543/50000000000000000000)
  directionHi := (526392911275807473087/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree112.table
  base := (59920043505074614215300033371425716173079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-607956960273126643297995136228374822000000000000)
      constant := (18098367456903202987166783172371678200578744289999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree112.table
  base := (14980010874401081154942553891625439038387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-7102118155112411203402130545239000000000000)
      constant := (211649349869940371959676029814277398394974806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263196455637903736543/50000000000000000000)
  centralHi := (526392911275807473087/100000000000000000000)
  directionLo := (264379367016683077303/50000000000000000000)
  directionHi := (528758734033366154607/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree113.table
  base := (61821727376688828340717131783928266066603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-613383085294316863219862426750157724500000000000)
      constant := (18428862551269962195284574199133758778287375359043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree113.table
  base := (30910863685162953377067982964624633706371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-7165505861668011080218339915194000000000000)
      constant := (215514136853849493742892942474080438096376699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264379367016683077303/50000000000000000000)
  centralHi := (528758734033366154607/100000000000000000000)
  directionLo := (531114018447749104723/100000000000000000000)
  directionHi := (132778504611937276181/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree114.table
  base := (12749990173955610841678088171917607289139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-68756578923945231460192190807993403000000000000)
      constant := (2084707121361039915639972220804284133979034208255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree114.table
  base := (3187497543217936830309274595656178808817/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-7228893568223610957034549285149000000000000)
      constant := (219414079283394054355831781346729942186900730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531114018447749104723/100000000000000000000)
  centralHi := (132778504611937276181/25000000000000000000)
  directionLo := (266729452051542250251/50000000000000000000)
  directionHi := (533458904103084500503/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree115.table
  base := (32852356991646219517793157457850955286241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 68445000000000000000000000000000000000000000
      center := (1012986)
      previous := (506493)
      next := (506493)
      square := (4944241111336790391664330856490000000000000)
      linear := (-590014494647161912158409270126392750000000000)
      constant := (18051863969597156554454960031582274890975853049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree115.table
  base := (65704713978677117614012885877470661916279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-14584562549558421667701517310208000000000000)
      constant := (446698354316974764878022994473181291863851151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266729452051542250251/50000000000000000000)
  centralHi := (533458904103084500503/100000000000000000000)
  directionLo := (535793527529039710701/100000000000000000000)
  directionHi := (267896763764519855351/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree116.table
  base := (8460752089546040288634992514899154065343/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-314830730178943761492732149157753216000000000000)
      constant := (9719193257008502597824199819779732944696016371932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree116.table
  base := (67686016712437992221333806142703582762417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-14711337962669621421333936050118000000000000)
      constant := (454638860958116479257852126543474905486848473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535793527529039710701/100000000000000000000)
  centralHi := (267896763764519855351/50000000000000000000)
  directionLo := (538118022293585483397/100000000000000000000)
  directionHi := (269059011146792741699/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree117.table
  base := (69693859068298548386816057629020123713317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (382132156899285867074356201780000000000000)
      linear := (-46394008720803400022450989030410500000000000)
      constant := (1445022090349468848690110293507730848569344693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree117.table
  base := (17423464766237943891509468717813901175307/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (361183513137321235419996410000000000000)
      linear := (-43899743715327873298717026006000000000000)
      constant := (1368786031035789088785367766419502802350614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538118022293585483397/100000000000000000000)
  centralHi := (269059011146792741699/50000000000000000000)
  directionLo := (108086503818433815101/20000000000000000000)
  directionHi := (270216259546084537753/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree118.table
  base := (71728241038507432172667549585480007348867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-640513710400267962829198879359072237000000000000)
      constant := (20126434722160244444139320520651835049159180752027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree118.table
  base := (71728241035657766074947167955924815683051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-14964888788892020928598773529938000000000000)
      constant := (470730806912820704566962460818015293850435619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108086503818433815101/20000000000000000000)
  centralHi := (270216259546084537753/50000000000000000000)
  directionLo := (542737145833464784879/100000000000000000000)
  directionHi := (6784214322918309811/1250000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree119.table
  base := (36894581313264825498545686613809057361267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-322969917710729091375533084940427569750000000000)
      constant := (10237484248056365846819618277598673389611087616427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree119.table
  base := (73789162624103417191360058369239854781129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-15091664202003220682231192269848000000000000)
      constant := (478882246226211976562294018880502285458010801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542737145833464784879/100000000000000000000)
  centralHi := (6784214322918309811/1250000000000000000)
  directionLo := (545032027721861085031/100000000000000000000)
  directionHi := (68129003465232635629/12500000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree120.table
  base := (2371144494749764042140980088389492038259/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (59541066)
      previous := (29770533)
      next := (29770533)
      square := (290611505321906901910047891453690000000000000)
      linear := (-36186997802369355704051858911257669000000000000)
      constant := (1157028262036035639792441323738841847790584571696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree120.table
  base := (2371144494685214573885587697032714860463/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-7609219807557210217931805504879000000000000)
      constant := (243551998215104686612170250605006460982691952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545032027721861085031/100000000000000000000)
  centralHi := (68129003465232635629/12500000000000000000)
  directionLo := (17103665229276090137/3125000000000000000)
  directionHi := (109463457467366976877/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree121.table
  base := (38995312327300319436711253024913811429889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-328396042731919311297400375462210472250000000000)
      constant := (10590527691882918155580057253352745637833686525609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree121.table
  base := (77990624652842211824812315485413964974763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-15345215028225620189496029749668000000000000)
      constant := (495396057524764577154128892535576710080734947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17103665229276090137/3125000000000000000)
  centralHi := (109463457467366976877/20000000000000000000)
  directionLo := (549593044709355295061/100000000000000000000)
  directionHi := (274796522354677647531/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree122.table
  base := (80131165094123956873027870953685929022221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-662218210485028842516668041446203847000000000000)
      constant := (21538608497462648635369401887928868165544261949301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree122.table
  base := (80131165092627107305462816095450368777987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-15471990441336819943128448489578000000000000)
      constant := (503758429509840011832482489758477112323479803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549593044709355295061/100000000000000000000)
  centralHi := (274796522354677647531/50000000000000000000)
  directionLo := (551859417395451662757/100000000000000000000)
  directionHi := (275929708697725831379/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree123.table
  base := (41149122575193207355589380989578245951503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (59541066)
      previous := (29770533)
      next := (29770533)
      square := (290611505321906901910047891453690000000000000)
      linear := (-37091351972567725691029740664888152750000000000)
      constant := (1216620447652100226140384404382798407748355377327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree123.table
  base := (41149122574556156020432814064075648500321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-7799382927224009848380433614744000000000000)
      constant := (256095556192703537785022260978765159596554249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551859417395451662757/100000000000000000000)
  centralHi := (275929708697725831379/50000000000000000000)
  directionLo := (554116520547073444023/100000000000000000000)
  directionHi := (69264565068384180503/12500000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree124.table
  base := (42245932411628662543149966412485304166327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-336535230263704641180201311244884826000000000000)
      constant := (11131367032295178123510684131714521603774677810287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree124.table
  base := (5280741551385805628793810780558029952469/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-7862770633779609725196642984699000000000000)
      constant := (260347053075722327093915473232875456495738088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554116520547073444023/100000000000000000000)
  centralHi := (69264565068384180503/12500000000000000000)
  directionLo := (69545558372545348527/12500000000000000000)
  directionHi := (556364466980362788217/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree125.table
  base := (43356012056321872836772238784842500582983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-339248292774299751141134956505776277250000000000)
      constant := (11314653259009816062386637072202982392878222817823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree125.table
  base := (86712024111720800605716621463452052190451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-15852316680670419204025704709308000000000000)
      constant := (529267410807937868797528136799417146820186219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69545558372545348527/12500000000000000000)
  centralHi := (556364466980362788217/100000000000000000000)
  directionLo := (558603367241454358439/100000000000000000000)
  directionHi := (13965084181036358961/2500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree126.table
  base := (88958723018484117616735451101925085007857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64580334515979311535566198100820000000000000)
      linear := (-8443490253948021261779471648559697000000000000)
      constant := (283936857012656616376484565940235483087287423657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree126.table
  base := (88958723017698661839569413311668232550591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-15979092093781618957658123449218000000000000)
      constant := (537911026354877021868794098624459931301049879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558603367241454358439/100000000000000000000)
  centralHi := (13965084181036358961/2500000000000000000)
  directionLo := (22433333186796439261/4000000000000000000)
  directionHi := (280416664834955490763/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree127.table
  base := (11403995192592863990885552095985617804727/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-344674417795489971063002247027559179750000000000)
      constant := (11685735382303380184845017338320066055901331622748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree127.table
  base := (91231961540074504068653478766111757047659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-16105867506892818711290542189128000000000000)
      constant := (546624952792256710523409440034677636941054371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22433333186796439261/4000000000000000000)
  centralHi := (280416664834955490763/50000000000000000000)
  directionLo := (11261089209197962521/2000000000000000000)
  directionHi := (563054460459898126051/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree128.table
  base := (2922866864981441438322576775477919367829/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-347387480306085081023935892288450631000000000000)
      constant := (11873531278882127027476571635027752232346651435984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree128.table
  base := (11691467459854669675301698036777433361247/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-8116321460002009232461480464519000000000000)
      constant := (277704595060037540424935163281533544952202972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11261089209197962521/2000000000000000000)
  centralHi := (563054460459898126051/100000000000000000000)
  directionLo := (565266863719194945737/100000000000000000000)
  directionHi := (282633431859597472869/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree129.table
  base := (95858057434477497298582396187480045227351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-77800120625928931329971008344298240500000000000)
      constant := (2680628977499743782942307019412070893788458660759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree129.table
  base := (47929028716996771509989344943730179625183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-8179709166557609109277689834474000000000000)
      constant := (282131869169166600563724776224093275356655927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (565266863719194945737/100000000000000000000)
  centralHi := (282633431859597472869/50000000000000000000)
  directionLo := (567470641526134671837/100000000000000000000)
  directionHi := (283735320763067335919/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree130.table
  base := (12276364350746915162400730352173296323369/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3170826)
      previous := (1585413)
      next := (1585413)
      square := (15476352354421077616511426172090000000000000)
      linear := (-2087654469392161544058006998877121500000000000)
      constant := (72506702614814239145530429269098752577890153124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree130.table
  base := (6138182175347722353539117146048253090877/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (361183513137321235419996410000000000000)
      linear := (-48775721142681709976886977541000000000000)
      constant := (1695824252801877323385825278123386024727016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567470641526134671837/100000000000000000000)
  centralHi := (283735320763067335919/50000000000000000000)
  directionLo := (71208236748070308957/12500000000000000000)
  directionHi := (569665893984562471657/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree131.table
  base := (25147577948482444952387324816154670107469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-355526667837870410906736828071124984750000000000)
      constant := (12445938308346514484937474146153782861828071943178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree131.table
  base := (100590311793579458177246100888379874363353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-16612969159337617725820217148768000000000000)
      constant := (582183767446184500990915074024232948767406657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71208236748070308957/12500000000000000000)
  centralHi := (569665893984562471657/100000000000000000000)
  directionLo := (571852719276894492783/100000000000000000000)
  directionHi := (35740794954805905799/6250000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree132.table
  base := (20599249679676139746203936613595551436443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-79608828966325671303926771851559208000000000000)
      constant := (2808832688461714540116233204376776969978624828935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree132.table
  base := (321863276244008336446029256967272699369/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-8369872286224408739726317944339000000000000)
      constant := (295624624167895049343819175633958053790937760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571852719276894492783/100000000000000000000)
  centralHi := (35740794954805905799/6250000000000000000)
  directionLo := (35876950857209854137/6250000000000000000)
  directionHi := (574031213715357666193/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree133.table
  base := (26357181154843917076523466961108484970709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-360952792859060630828604118592907887250000000000)
      constant := (12835059111097381564269709203721175688747412060058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree133.table
  base := (105428724619122136720062689439299094660561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-16866519985560017233085054628588000000000000)
      constant := (600385040115859601047159583989119296997634809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35876950857209854137/6250000000000000000)
  centralHi := (574031213715357666193/100000000000000000000)
  directionLo := (288100735895742965131/50000000000000000000)
  directionHi := (576201471791485930263/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree134.table
  base := (53943870228484234349686779166556458603917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-363665855369655740789537763853799338500000000000)
      constant := (13031874347405707610197523556948815148938801481077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree134.table
  base := (53943870228376402046576698353414821054287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-8496647699335608493358736684249000000000000)
      constant := (304795571393201146358599554142903104758174503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288100735895742965131/50000000000000000000)
  centralHi := (576201471791485930263/100000000000000000000)
  directionLo := (9036931034749138229/1562500000000000000)
  directionHi := (578363586223944846657/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree135.table
  base := (55186647955608876435961254764891348473217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32290167257989655767783099050410000000000000)
      linear := (-4523196517040133959882363075490009750000000000)
      constant := (163335713666702542413062480742884806171416573017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree135.table
  base := (27593323977758577349659394735440400509677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-8560035405891208370174946054204000000000000)
      constant := (309433778173714126396484212098853230372270826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9036931034749138229/1562500000000000000)
  centralHi := (578363586223944846657/100000000000000000000)
  directionLo := (29025882400237654713/5000000000000000000)
  directionHi := (580517648004753094261/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree136.table
  base := (56442695491092973096936878744353311633381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-369091980390845960711405054375582241000000000000)
      constant := (13430014489889202566117189527425369629480207477261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree136.table
  base := (112885390982029918192057918336912632392887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-17246846224893616493982310848318000000000000)
      constant := (628214280798948173153354245015406234874397903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29025882400237654713/5000000000000000000)
  centralHi := (580517648004753094261/100000000000000000000)
  directionLo := (58266374644396603577/10000000000000000000)
  directionHi := (582663746443966035771/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree137.table
  base := (5771201283496916429008285600221253875311/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-371805042901441070672338699636473692250000000000)
      constant := (13631339396064833863806763374052605175318972255910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree137.table
  base := (57712012834902812899066210091520510418769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-8686810819002408123807364794114000000000000)
      constant := (318815658070486603504116956816521841260771961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58266374644396603577/10000000000000000000)
  centralHi := (582663746443966035771/100000000000000000000)
  directionLo := (18275061537902607537/3125000000000000000)
  directionHi := (116960393842576688237/20000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree138.table
  base := (117989199974542270285051510093786447628651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15210000000000000000000000000000000000000000
      center := (225108)
      previous := (112554)
      next := (112554)
      square := (1098720246963731198147629079220000000000000)
      linear := (-157327496497389699908957086703367000000000000)
      constant := (5811454537084664464916972111112929249343178171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree138.table
  base := (29497299993607352898598207267992429391097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-8750198525558008000623574164069000000000000)
      constant := (323559331186757421436205147443318441134190786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18275061537902607537/3125000000000000000)
  centralHi := (116960393842576688237/20000000000000000000)
  directionLo := (293466201192920256017/50000000000000000000)
  directionHi := (117386480477168102407/20000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree139.table
  base := (12058091389606659700698801685139770584419/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-377231167922631290594205990158256594750000000000)
      constant := (14038498878285081450895299295731618133571207922695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree139.table
  base := (120580913895970619872135190092824867295263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-17627172464227215754879567068048000000000000)
      constant := (656676319496584799931112420396248152572899447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293466201192920256017/50000000000000000000)
  centralHi := (117386480477168102407/20000000000000000000)
  directionLo := (294527565240319284693/50000000000000000000)
  directionHi := (589055130480638569387/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree140.table
  base := (123199167434581063766843510159737838792153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-759888460866452801110279270838296092000000000000)
      constant := (28488666908660399010234482097257642498344438898593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree140.table
  base := (61599583717249723570279541305901927649823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-8876973938669207754255992903979000000000000)
      constant := (333152143755097470697197509537382425772820087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294527565240319284693/50000000000000000000)
  centralHi := (589055130480638569387/100000000000000000000)
  directionLo := (591170236497669137493/100000000000000000000)
  directionHi := (295585118248834568747/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree141.table
  base := (125843960590155920238950626699252611157371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-85034953987515891225794062373342110500000000000)
      constant := (3211482500814589394942587857177025102913846122939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree141.table
  base := (125843960590086518897325052582905441028011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-17880723290449615262144404547868000000000000)
      constant := (676002566414357202971362723188412769533733859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591170236497669137493/100000000000000000000)
  centralHi := (295585118248834568747/50000000000000000000)
  directionLo := (593277801957782664657/100000000000000000000)
  directionHi := (296638900978891332329/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree142.table
  base := (128515293362861552929118104321377283208919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-770740710908833240954013851881861897000000000000)
      constant := (29321024552583389237081494808255135810751505969039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree142.table
  base := (64257646681401270776396386362024883693027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-9003749351780407507888411643889000000000000)
      constant := (342885578104541767022683158713260205344121563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593277801957782664657/100000000000000000000)
  centralHi := (296638900978891332329/50000000000000000000)
  directionLo := (148844476734737691181/25000000000000000000)
  directionHi := (23815116277558030589/4000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree143.table
  base := (5248526630110727675383249017978086827351/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (6341652)
      previous := (3170826)
      next := (3170826)
      square := (30952704708842155233022852344180000000000000)
      linear := (-4592703171183570774413497884045235500000000000)
      constant := (175986467718444743358472057860601331389754074975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree143.table
  base := (131213165752718017442927703811269629635681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (148)
      previous := (74)
      next := (74)
      square := (722367026274642470839992820000000000000)
      linear := (-107303397140071093310113858152000000000000)
      constant := (4116035839611750588823573755386019629635681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148844476734737691181/25000000000000000000)
  centralHi := (23815116277558030589/4000000000000000000)
  directionLo := (149367657527942157203/25000000000000000000)
  directionHi := (597470630111768628813/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree144.table
  base := (33484394439986417888522277665511719354881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32290167257989655767783099050410000000000000)
      linear := (-4824647907106257288874990326700171000000000000)
      constant := (186206222116253873029740134911043915444091432562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree144.table
  base := (133937577759903012762270679723401953366461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-18261049529783214523041660767598000000000000)
      constant := (705519268470275990555693065815086930118931909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149367657527942157203/25000000000000000000)
  centralHi := (597470630111768628813/100000000000000000000)
  directionLo := (599556048773842140067/100000000000000000000)
  directionHi := (149889012193460535017/25000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree145.table
  base := (34172132346115809261916697094469151138851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-393509542986201950359807861723605302250000000000)
      constant := (15296054683915894041969228096258094937717798256662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree145.table
  base := (68344264692213484924148491863926479049583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-9193912471447207138337039753754000000000000)
      constant := (357749395468382846466963471881630449959379527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599556048773842140067/100000000000000000000)
  centralHi := (149889012193460535017/25000000000000000000)
  directionLo := (120326847776620443493/20000000000000000000)
  directionHi := (300817119441551108733/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree146.table
  base := (69733010313194694211062670474244478281657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-396222605496797060320741506984496753500000000000)
      constant := (15510908599706819814401668581330509511862781814017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree146.table
  base := (17433252578294819574779059752886686164929/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-9257300178002807015153249123709000000000000)
      constant := (362774312146933280760258384608150399847492004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120326847776620443493/20000000000000000000)
  centralHi := (300817119441551108733/50000000000000000000)
  directionLo := (1886578984656521911/312500000000000000)
  directionHi := (603705275090087011521/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree147.table
  base := (35567512871447939194964787150486938202093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (59541066)
      previous := (29770533)
      next := (29770533)
      square := (290611505321906901910047891453690000000000000)
      linear := (-44326185334154685586852794693932022750000000000)
      constant := (1747473970976620656375307929163994531196258193274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree147.table
  base := (71135025742882773469001757760126375042029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-9320687884558406891969458493664000000000000)
      constant := (367834384270795025054472047908093732382102901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1886578984656521911/312500000000000000)
  centralHi := (603705275090087011521/100000000000000000000)
  directionLo := (60576923076923076923/10000000000000000000)
  directionHi := (605769230769230769231/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree148.table
  base := (145100621962737006948405432863285325366497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-803297461035974560485217595012559312000000000000)
      constant := (31890252202328867393877051945855150145970306062057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree148.table
  base := (145100621962714727223437929848879537982473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-18768151182228013537571335727238000000000000)
      constant := (745859223679947445593343827446314641919037937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60576923076923076923/10000000000000000000)
  centralHi := (605769230769230769231/100000000000000000000)
  directionLo := (607826178049196472023/100000000000000000000)
  directionHi := (75978272256149559003/12500000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree149.table
  base := (147957732057290762334959390926466558998201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-808723586057164780407084885534342214500000000000)
      constant := (32328979373663201576824224109142114804698976575681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree149.table
  base := (73978866028635912131962576223532033263837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-9447463297669606645601877233574000000000000)
      constant := (378059994854474927902251389009859788621588453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607826178049196472023/100000000000000000000)
  centralHi := (75978272256149559003/12500000000000000000)
  directionLo := (152469046960571930891/25000000000000000000)
  directionHi := (121975237568457544713/20000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree150.table
  base := (150841381769517548247436263706335567808529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-90461079008706111147661352895125013000000000000)
      constant := (3641190332398071291376482953500895756441352710161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree150.table
  base := (150841381769501451341961802298468838032941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-19021702008450413044836173207058000000000000)
      constant := (766451066628608200387162876144641233627567029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152469046960571930891/25000000000000000000)
  centralHi := (121975237568457544713/20000000000000000000)
  directionLo := (611919329872973819193/100000000000000000000)
  directionHi := (305959664936486909597/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree151.table
  base := (76875785549740375280961225185578601479101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-409787918049772610125409733288954009750000000000)
      constant := (16607726528043823269093383688444198439219044288581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree151.table
  base := (153751571099467069178168494287471019239607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-19148477421561612798468591946968000000000000)
      constant := (776852454438933204203109005736539352251493583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611919329872973819193/100000000000000000000)
  centralHi := (305959664936486909597/50000000000000000000)
  directionLo := (61395567270556046073/10000000000000000000)
  directionHi := (613955672705560460731/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree152.table
  base := (31337660009448517422497900861332873428157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-825001961120735440172686757099690922000000000000)
      constant := (33663199567178666873482776801766390502027018902585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree152.table
  base := (78344150023615479638592845905925378669509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-9637626417336406276050505343439000000000000)
      constant := (393662076569967696413312702554819388995147021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61395567270556046073/10000000000000000000)
  centralHi := (613955672705560460731/100000000000000000000)
  directionLo := (615985283771037185239/100000000000000000000)
  directionHi := (15399632094275929631/2500000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree153.table
  base := (9978223038304005599858210097274397789683/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32290167257989655767783099050410000000000000)
      linear := (-5126099297172380617867617577910332250000000000)
      constant := (210579953857136694988655188708126569595926099064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree153.table
  base := (79825784306427103749726627500052554794699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-9701014123892006152866714713394000000000000)
      constant := (398933081365812544884063205312827756760304131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615985283771037185239/100000000000000000000)
  centralHi := (15399632094275929631/2500000000000000000)
  directionLo := (309004114696565624913/50000000000000000000)
  directionHi := (618008229393131249827/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree154.table
  base := (81320688398202547075579869982302234211823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-417927105581557940008210669071628363500000000000)
      constant := (17283855964560256492224398625892687547583716229863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree154.table
  base := (162641376796396696049159746667978119700243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-19528803660895212059365848166698000000000000)
      constant := (808478483214012415120119889400450302229341067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309004114696565624913/50000000000000000000)
  centralHi := (618008229393131249827/100000000000000000000)
  directionLo := (124004914962719290611/20000000000000000000)
  directionHi := (9687883981462444579/1562500000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree155.table
  base := (165657724597924239019997138484242701159563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-841280336184306099938288628665039629500000000000)
      constant := (35024477779972196690095881873913209066163778432803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree155.table
  base := (33131544919583420471932938224008878716707/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-19655579074006411812998266906608000000000000)
      constant := (819161114587107285368843601041496252515617415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124004914962719290611/20000000000000000000)
  centralHi := (9687883981462444579/1562500000000000000)
  directionLo := (622034384216764173309/100000000000000000000)
  directionHi := (62203438421676417331/10000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree156.table
  base := (21087576502184871005948320227410137785187/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (352314)
      previous := (176157)
      next := (176157)
      square := (1719594706046786401834602908010000000000000)
      linear := (-278338744643489914483943431685346000000000000)
      constant := (11664776488300990034057702098010111538981101228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree156.table
  base := (168700612017472903602932401453473404924443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (148)
      previous := (74)
      next := (74)
      square := (722367026274642470839992820000000000000)
      linear := (-117055351994778766666453761222000000000000)
      constant := (4910734064206623752404494168415473404924443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622034384216764173309/100000000000000000000)
  centralHi := (62203438421676417331/10000000000000000000)
  directionLo := (62403772075338276227/10000000000000000000)
  directionHi := (624037720753382762271/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree157.table
  base := (85885019527562769432944727448736664010099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-426066293113343269891011604854302717250000000000)
      constant := (17973514410719582676772347386331450137846578216619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree157.table
  base := (171770039055120385756128298322075296886163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-19909129900228811320263104386428000000000000)
      constant := (840737310005458313812808585753100475173761547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62403772075338276227/10000000000000000000)
  centralHi := (624037720753382762271/100000000000000000000)
  directionLo := (78254330820471293029/12500000000000000000)
  directionHi := (626034646563770344233/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree158.table
  base := (10929125356932439680158009785018726386337/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-428779355623938379851945250115194168500000000000)
      constant := (18206407006027628292684544633678886592948114360776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree158.table
  base := (174866005710914656332559163193524281304917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-20035905313340011073895523126338000000000000)
      constant := (851630874050733297507939660982189603540530973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78254330820471293029/12500000000000000000)
  centralHi := (626034646563770344233/100000000000000000000)
  directionLo := (314012611400152518247/50000000000000000000)
  directionHi := (125605044560061007299/20000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree159.table
  base := (177988511984913380296745770287058905752953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (119082132)
      previous := (59541066)
      next := (59541066)
      square := (581223010643813803820095782907380000000000000)
      linear := (-95887204029896331069528643416907915500000000000)
      constant := (4097956183251141763348996934939750562427102760377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree159.table
  base := (44497127996227415007671431421212770000723/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-10081340363225605413763970933124000000000000)
      constant := (431297374493376740947896301727380291260244374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314012611400152518247/50000000000000000000)
  centralHi := (125605044560061007299/20000000000000000000)
  directionLo := (315004754824637809807/50000000000000000000)
  directionHi := (126001901929855123923/20000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree160.table
  base := (181137557877161357504893328275335821488473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-868410961290257199547625081273954142000000000000)
      constant := (37353403733054605430580654682952043339928168948513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree160.table
  base := (90568778938579098339150891939522770692663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-10144728069781205290580180303079000000000000)
      constant := (436814467406763895073632282523419348247060047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315004754824637809807/50000000000000000000)
  centralHi := (126001901929855123923/20000000000000000000)
  directionLo := (78998445794014343287/12500000000000000000)
  directionHi := (631987566352114746297/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree161.table
  base := (184313143387714626362315635097333691218063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 136890000000000000000000000000000000000000000
      center := (2025972)
      previous := (1012986)
      next := (1012986)
      square := (9888482222673580783328661712980000000000000)
      linear := (-1651865947658690774044409020407820500000000000)
      constant := (71508900308957692553022832180716373352209064407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree161.table
  base := (36862628677542388190557859544606572775033/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-20416231552673610334792779346068000000000000)
      constant := (884733431531064955282833096989454303994902885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78998445794014343287/12500000000000000000)
  centralHi := (631987566352114746297/100000000000000000000)
  directionLo := (316979725613017940873/50000000000000000000)
  directionHi := (633959451226035881747/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree162.table
  base := (37503053703324748971583930383451595116999/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64580334515979311535566198100820000000000000)
      linear := (-10855101374477007893720489658240987000000000000)
      constant := (472913817782872639194596432178232608337774137995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree162.table
  base := (18751526851662146344568728966894801968407/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-10271503482892405044212599042989000000000000)
      constant := (447954119569686761866234147038509107663303915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316979725613017940873/50000000000000000000)
  centralHi := (633959451226035881747/100000000000000000000)
  directionLo := (127185044336818862791/20000000000000000000)
  directionHi := (158981305421023578489/25000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree163.table
  base := (95371966631969095416455719263473241163681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-442344668176913929656613476419651424750000000000)
      constant := (19393418331988578483033683865266570047934276351561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree163.table
  base := (95371966631968126356619580310582191090599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-10334891189448004921028808412944000000000000)
      constant := (453576678819230929531087645531184765294311231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127185044336818862791/20000000000000000000)
  centralHi := (158981305421023578489/25000000000000000000)
  directionLo := (637884934254691757597/100000000000000000000)
  directionHi := (318942467127345878799/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree164.table
  base := (193999137629706384438406472788534343887137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72414810000000000000000000000000000000000000000
      center := (1071739188)
      previous := (535869594)
      next := (535869594)
      square := (5231007095794324234380862046166420000000000000)
      linear := (-890115461375018079235094243361085752000000000000)
      constant := (39270660534132389568068568257632430145856168729897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree164.table
  base := (24249892203713092252036191972246877462319/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-10398278896003604797845017782899000000000000)
      constant := (459234393514169072908518414802009889164527644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637884934254691757597/100000000000000000000)
  centralHi := (318942467127345878799/50000000000000000000)
  directionLo := (63983864460054329781/10000000000000000000)
  directionHi := (639838644600543297811/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree165.table
  base := (9864044080698785553986655073530300807969/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (59541066)
      previous := (29770533)
      next := (29770533)
      square := (290611505321906901910047891453690000000000000)
      linear := (-49752310355344905508720085215714925250000000000)
      constant := (2208749491715484706737681950534490397754553791210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree165.table
  base := (197280881613974312504728589487862588574013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-20923333205118409349322454305708000000000000)
      constant := (929854527309010393439384349166862527469008197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63983864460054329781/10000000000000000000)
  centralHi := (639838644600543297811/100000000000000000000)
  directionLo := (641786407537124678253/100000000000000000000)
  directionHi := (320893203768562339127/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree166.table
  base := (100294582608396272319922991642698552275827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-450483855708699259539414412202325778500000000000)
      constant := (20123663807108249120644400335712234870564157979787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree166.table
  base := (200589165216791356645181844179632590952481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122080027440414577571958786580000000000000)
      linear := (-21050108618229609102954873045618000000000000)
      constant := (941310578480486440228077563041365907870969289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641786407537124678253/100000000000000000000)
  centralHi := (320893203768562339127/50000000000000000000)
  directionLo := (40233017315663576851/6250000000000000000)
  directionHi := (643728277050617229617/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree167.table
  base := (101961994219101135405842052775552617614251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36207405000000000000000000000000000000000000000
      center := (535869594)
      previous := (267934797)
      next := (267934797)
      square := (2615503547897162117190431023083210000000000000)
      linear := (-453196918219294369500348057463217229750000000000)
      constant := (20370085412073019393866617226933663477305426445731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree167.table
  base := (101961994219100630863563435504298172644663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-10588442015670404428293645892764000000000000)
      constant := (476418470271386978655519090376388766176948047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40233017315663576851/6250000000000000000)
  centralHi := (643728277050617229617/100000000000000000000)
  directionLo := (645664306315367058491/100000000000000000000)
  directionHi := (161416076578841764623/25000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree168.table
  base := (103642675639124655200337827117785485115791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4023045000000000000000000000000000000000000000
      center := (59541066)
      previous := (29770533)
      next := (29770533)
      square := (290611505321906901910047891453690000000000000)
      linear := (-50656664525543275495697966969345409000000000000)
      constant := (2290890026703759335168338297916665713393531480719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree168.table
  base := (51821337819562113328297602084166279555317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61040013720207288785979393290000000000000)
      linear := (-10651829722226004305109855262719000000000000)
      constant := (482216806747940226304175060542130202489697146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell103.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645664306315367058491/100000000000000000000)
  centralHi := (161416076578841764623/25000000000000000000)
  directionLo := (647594547710874470581/100000000000000000000)
  directionHi := (323797273855437235291/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree169.table
  base := (26334156717122142810607826107847346013713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3170826)
      previous := (1585413)
      next := (1585413)
      square := (15476352354421077616511426172090000000000000)
      linear := (-2713745817991033073504232828313610250000000000)
      constant := (123475966224206215473659479021443076631428853348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree169.table
  base := (52668313434244103631243134281078034328491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (361183513137321235419996410000000000000)
      linear := (-63403653424743220011396832146000000000000)
      constant := (2887871589762761167951372182598031068656982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell103.Kernel169
