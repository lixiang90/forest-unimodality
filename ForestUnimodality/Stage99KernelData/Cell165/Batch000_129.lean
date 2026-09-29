import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell165.Parameters
import ForestUnimodality.BinomialMassData.Q13_23.Batch000_049
import ForestUnimodality.BinomialMassData.Q13_23.Batch050_099
import ForestUnimodality.BinomialMassData.Q13_23.Batch100_149
import ForestUnimodality.BinomialMassData.Q21_37.Batch000_049
import ForestUnimodality.BinomialMassData.Q21_37.Batch050_099
import ForestUnimodality.BinomialMassData.Q21_37.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree000.table
  base := (222682322432607579420960061/10000000000000000000000000)
  polynomial :=
    { denominator := 57500000000000000000000000000000000000000
      center := (169)
      previous := (0)
      next := (130)
      square := (4256458488937116049766196135000000000000)
      linear := (-15320762523585010200788403200000000000000)
      constant := (1280423353987493581670520350750000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree000.table
  base := (222682322432607579420960061/10000000000000000000000000)
  polynomial :=
    { denominator := 92500000000000000000000000000000000000000
      center := (273)
      previous := (0)
      next := (208)
      square := (6847346264811882340928228565000000000000)
      linear := (-24646444059680233801268300800000000000000)
      constant := (2059811482501620109643880564250000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree001.table
  base := (17044687355752324977526391529761385306013/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-463045458754820251912054373110000000000000)
      constant := (18263724851915624637633627442992545653761754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree001.table
  base := (136003835152039497513187494631510588911089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-4798027893321070835863650917320000000000000)
      constant := (188586003483915432287546633503917996219280841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (4954135886438745953/10000000000000000000)
  directionHi := (49541358864387459531/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree002.table
  base := (86098264625377167999972954154488601921289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-2294853517868741076823901890480000000000000)
      constant := (47639752756846317793674982087004470416361881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree002.table
  base := (5355697768220936695648351947913210558947/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-1487095516452366767284898329060000000000000)
      constant := (30689403489044639717710059986552741020793772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4954135886438745953/10000000000000000000)
  centralHi := (49541358864387459531/100000000000000000000)
  directionLo := (35031030802204649897/50000000000000000000)
  directionHi := (14012412320881859959/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree003.table
  base := (7020974045291382481685788280675844783513/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-684381300179550286499896572130000000000000)
      constant := (8307181728845635172658415391900043780956754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree003.table
  base := (27905157993985747307597175656339332722133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-3549368119148931651207767857580000000000000)
      constant := (42776646614207190010149211762138546496600077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35031030802204649897/50000000000000000000)
  centralHi := (14012412320881859959/20000000000000000000)
  directionLo := (85808150629121856989/100000000000000000000)
  directionHi := (8580815062912185699/10000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree004.table
  base := (1890881004216683955173578610444196963461/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-795049220891915303793817671640000000000000)
      constant := (6298471374948504452682407797504900968354345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree004.table
  base := (37532699515298110609845896662420799812407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-8249090410786259535691478114080000000000000)
      constant := (64886700596659200825087838978534074943185183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85808150629121856989/100000000000000000000)
  centralHi := (8580815062912185699/10000000000000000000)
  directionLo := (99082717728774919061/100000000000000000000)
  directionHi := (49541358864387459531/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree005.table
  base := (5231574604162428315792179936029990886727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-3622868566417121284350955084600000000000000)
      constant := (20948484756447693427520897053299325895392915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree005.table
  base := (162122805414480466162396601472649561199/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-2349861145818663942241855128250000000000000)
      constant := (13506045574264753330476110019267289971257240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99082717728774919061/100000000000000000000)
  centralHi := (49541358864387459531/50000000000000000000)
  directionLo := (110777846118482144683/100000000000000000000)
  directionHi := (27694461529620536171/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree006.table
  base := (3687262466784806608067775656990525392387/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-4065540249266581353526639482640000000000000)
      constant := (19036590340124930408250907069459939662863615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree006.table
  base := (3654266975501966612819566017217926807583/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-10549798755763052002243362911920000000000000)
      constant := (49187532204757739197300132093536708997905635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110777846118482144683/100000000000000000000)
  centralHi := (27694461529620536171/25000000000000000000)
  directionLo := (121351050381857558451/100000000000000000000)
  directionHi := (30337762595464389613/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree007.table
  base := (13087493331608235536515322162801008223471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-4508211932116041422702323880680000000000000)
      constant := (18630082008725397356792952918301733350216159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree007.table
  base := (405081017245751339760642537012069496943/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-2925038232062862058879826327710000000000000)
      constant := (12058509859711164812253594338661185130519736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121351050381857558451/100000000000000000000)
  centralHi := (30337762595464389613/25000000000000000000)
  directionLo := (4096066098980453059/3125000000000000000)
  directionHi := (131074115167374497889/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree008.table
  base := (920920643863681850351293339802049741619/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-2475441807482750745939004139360000000000000)
      constant := (9625845448476759502401522001216421566582255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree008.table
  base := (9113781767187722383587381625563751427037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-12850507100739844468795247709760000000000000)
      constant := (49932096672039224429514053098516775703613653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4096066098980453059/3125000000000000000)
  centralHi := (131074115167374497889/100000000000000000000)
  directionLo := (35031030802204649897/25000000000000000000)
  directionHi := (140124123208818599589/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree009.table
  base := (1568168439781182180113050918419988936177/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-1348388824453740390263423169190000000000000)
      constant := (5155423374471525549608980105549174147237633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree009.table
  base := (6198858614387128026635105490449608365319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-14000861273228240702071190108680000000000000)
      constant := (53561549792792099789821997801805513852121711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35031030802204649897/25000000000000000000)
  centralHi := (140124123208818599589/100000000000000000000)
  directionLo := (4644502393536324331/3125000000000000000)
  directionHi := (148624076593162378593/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree010.table
  base := (990375003452323239403178449701919966009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-1459056745166105407557344268700000000000000)
      constant := (5643179177198298199792370106392315662018761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree010.table
  base := (780732970040875252164528765520250075971/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-15151215445716636935347132507600000000000000)
      constant := (58692316166083242762773180689986111770021495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4644502393536324331/3125000000000000000)
  centralHi := (148624076593162378593/100000000000000000000)
  directionLo := (156663532391237173769/100000000000000000000)
  directionHi := (15666353239123717377/10000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree011.table
  base := (2081679366535495821854721888605330534977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-6278898663513881699405061472840000000000000)
      constant := (25002131442348787664032800555492219853002833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree011.table
  base := (407168574277044693873076846709683140179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-16301569618205033168623074906520000000000000)
      constant := (65061058233057593836989467382707781094525255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156663532391237173769/100000000000000000000)
  centralHi := (15666353239123717377/10000000000000000000)
  directionLo := (164310098957520687909/100000000000000000000)
  directionHi := (16431009895752068791/10000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree012.table
  base := (510928756962528445987957714894489086223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-6721570346363341768580745870880000000000000)
      constant := (27845249959632598902282227861259184726611967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree012.table
  base := (474263849888595529600549453265418341141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-17451923790693429401899017305440000000000000)
      constant := (72501950628126922538545515817840357709022029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (164310098957520687909/100000000000000000000)
  centralHi := (16431009895752068791/10000000000000000000)
  directionLo := (85808150629121856989/50000000000000000000)
  directionHi := (171616301258243713979/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree013.table
  base := (-415062788845080817342220779192408216509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-3582121014606400918878215134460000000000000)
      constant := (15530041770066857130046560951297216053466739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree013.table
  base := (-859656190724313059201040786772273324669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-18602277963181825635174959704360000000000000)
      constant := (80907411887546504136943078200928757818528139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85808150629121856989/50000000000000000000)
  centralHi := (171616301258243713979/100000000000000000000)
  directionLo := (44655977410427854221/25000000000000000000)
  directionHi := (35724781928342283377/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree014.table
  base := (-1994550794770152842720492847940036469047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-7606913712062261906932114666960000000000000)
      constant := (34618559657615264751932291730559720707874137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree014.table
  base := (-1009223334607339327058935385687865975959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-9876316067835110934225451051640000000000000)
      constant := (45102764618516144099670854773033311478912129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44655977410427854221/25000000000000000000)
  centralHi := (35724781928342283377/20000000000000000000)
  directionLo := (185366791345754018241/100000000000000000000)
  directionHi := (92683395672877009121/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree015.table
  base := (-754708952916823458136760367178699165421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-2012396348727930494026949766250000000000000)
      constant := (9625343918694505109901984043387468141492291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree015.table
  base := (-3038227130512737817915163375631398334411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-20902986308158618101726844502200000000000000)
      constant := (100346855019574780871315819737260615680191341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185366791345754018241/100000000000000000000)
  centralHi := (92683395672877009121/50000000000000000000)
  directionLo := (47968214457564454399/25000000000000000000)
  directionHi := (191872857830257817597/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree016.table
  base := (-3928710626349105282922015115636242381129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-8492257077761182045283483463040000000000000)
      constant := (42694920422697162884057111480948427780382759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree016.table
  base := (-197223443600562543729306056207055638603/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-5513335120161753583750696725280000000000000)
      constant := (27824129757260823317329678629582704153762465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47968214457564454399/25000000000000000000)
  centralHi := (191872857830257817597/100000000000000000000)
  directionLo := (99082717728774919061/50000000000000000000)
  directionHi := (198165435457549838123/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree017.table
  base := (-1185678352897332029237501550725487044449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-2233732190152660528614791965270000000000000)
      constant := (11797346801993845784239372066411217353486479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree017.table
  base := (-951104798806995754387019492619147530003/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-23203694653135410568278729300040000000000000)
      constant := (123029397240093227655806234021441935157129465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99082717728774919061/50000000000000000000)
  centralHi := (198165435457549838123/100000000000000000000)
  directionLo := (8170570217379971581/4000000000000000000)
  directionHi := (102132127717249644763/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree018.table
  base := (-5474438070901256686997975140031426462347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-9377600443460102183634852259120000000000000)
      constant := (51977584855654148485906944471003375401418437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree018.table
  base := (-2742424260164248222165476173635502539493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-12177024412811903400777335849480000000000000)
      constant := (67763534178109130472813704484252997023434083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8170570217379971581/4000000000000000000)
  centralHi := (102132127717249644763/50000000000000000000)
  directionLo := (105093092406613949691/50000000000000000000)
  directionHi := (210186184813227899383/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree019.table
  base := (-6133992584203133094531783222880254118289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-9820272126309562252810536657160000000000000)
      constant := (57054166244356708859230039471516345571425119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree019.table
  base := (-6142445252360493585988688409568479983999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-25504402998112203034830614097880000000000000)
      constant := (148775838542207756947401900755080750901905369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105093092406613949691/50000000000000000000)
  centralHi := (210186184813227899383/100000000000000000000)
  directionLo := (21594577681554788017/10000000000000000000)
  directionHi := (215945776815547880171/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree020.table
  base := (-1682243416708800512414718815237248680101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-2565735952289755580496555263800000000000000)
      constant := (15603778177917018701319983740739495448226571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree020.table
  base := (-6735828619286404815959691041280165269937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-26654757170600599268106556496800000000000000)
      constant := (162765420544547925667648362780487453745456247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21594577681554788017/10000000000000000000)
  centralHi := (215945776815547880171/100000000000000000000)
  directionLo := (110777846118482144683/50000000000000000000)
  directionHi := (221555692236964289367/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree021.table
  base := (-7265136721548953514350424784049378561927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-10705615492008482391161905453240000000000000)
      constant := (68057379649532708134173880148057878740740617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree021.table
  base := (-454418021979693077311153062934350260699/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-6951277835772248875345624723930000000000000)
      constant := (44372006280522499748680819981516497972412276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110777846118482144683/50000000000000000000)
  centralHi := (221555692236964289367/100000000000000000000)
  directionLo := (227027027027027027027/100000000000000000000)
  directionHi := (56756756756756756757/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree022.table
  base := (-7746868115261517761280763645994584385969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-11148287174857942460337589851280000000000000)
      constant := (73978646669851446931667153476148864859822399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree022.table
  base := (-3875678823095131184618800588689966260727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-14477732757788695867329220647320000000000000)
      constant := (96468860064300675190741464788843436189064737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227027027027027027027/100000000000000000000)
  centralHi := (56756756756756756757/25000000000000000000)
  directionLo := (116184785190295551563/50000000000000000000)
  directionHi := (232369570380591103127/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree023.table
  base := (-4088762683455818347886561377712805422717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115000000000000000000000000000000000000000
      center := (338)
      previous := (0)
      next := (260)
      square := (8512916977874232099532392270000000000000)
      linear := (-251977366471900054989419005420000000000000)
      constant := (1742981253154471668040081865142605475277509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree023.table
  base := (-8181150566136143107593986027852108366957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-30105819688065787967934383693560000000000000)
      constant := (209109968611418504160868299862690463645635867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116184785190295551563/50000000000000000000)
  centralHi := (232369570380591103127/100000000000000000000)
  directionLo := (237592010549577411537/100000000000000000000)
  directionHi := (118796005274788705769/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree024.table
  base := (-213992163908272769836191379056673080433/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-3008407635139215649672239661840000000000000)
      constant := (21662872192766135219275164036470199404509430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree024.table
  base := (-2140652369893278141780774813312730867323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-7814043465138546050302581523120000000000000)
      constant := (56500322517166699646585259293694871442634813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237592010549577411537/100000000000000000000)
  centralHi := (118796005274788705769/50000000000000000000)
  directionLo := (121351050381857558451/50000000000000000000)
  directionHi := (242702100763715116903/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree025.table
  base := (-1111916968565796984404995969858164199619/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-3119075555851580666966160761350000000000000)
      constant := (23350162619334814356040722119515062276803098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree025.table
  base := (-4448844513394030217492585586410940285599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-16203264016521290217243134245700000000000000)
      constant := (121804504298896740838089393103453422749014969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121351050381857558451/50000000000000000000)
  centralHi := (242702100763715116903/100000000000000000000)
  directionLo := (247706794321937297653/100000000000000000000)
  directionHi := (123853397160968648827/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree026.table
  base := (-2296500583620348262370210329511834481351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-3229743476563945684260081860860000000000000)
      constant := (25105953429024912086180869941068239559365321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree026.table
  base := (-9187894339315186291347998902322110754691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-33556882205530976667762210890320000000000000)
      constant := (261931063673728234205131832707601030376828021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247706794321937297653/100000000000000000000)
  centralHi := (123853397160968648827/50000000000000000000)
  directionLo := (252612355579414542933/100000000000000000000)
  directionHi := (126306177789707271467/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree027.table
  base := (-943286658909277697052256309061350890409/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-6680822794552621403108005920740000000000000)
      constant := (53860177060962649343315035024422726894868195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree027.table
  base := (-1886877141022533270549248116256393058243/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-34707236378019372901038153289240000000000000)
      constant := (280965866862256312932764229683844989516326665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252612355579414542933/100000000000000000000)
  centralHi := (126306177789707271467/50000000000000000000)
  directionLo := (257424451887365570967/100000000000000000000)
  directionHi := (32178056485920696371/12500000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree028.table
  base := (-1927368022989568428510186597339150192841/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-13804317271954702875391696239520000000000000)
      constant := (115289789457047519077168371179317947739935555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree028.table
  base := (-1927611656964431434844047400965722903939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-35857590550507769134314095688160000000000000)
      constant := (300712192688459290035225750587109626722537545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257424451887365570967/100000000000000000000)
  centralHi := (32178056485920696371/12500000000000000000)
  directionLo := (262148230334748995777/100000000000000000000)
  directionHi := (131074115167374497889/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree029.table
  base := (-4899313707315288345299589619382689062147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-7123494477402081472283690318780000000000000)
      constant := (61565873519799689899097902710356557486124237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree029.table
  base := (-1959920616437046261144706811270542554073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-37007944722996165367590038087080000000000000)
      constant := (321169095168214952691629991103033136217370315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262148230334748995777/100000000000000000000)
  centralHi := (131074115167374497889/50000000000000000000)
  directionLo := (266788382254120345157/100000000000000000000)
  directionHi := (133394191127060172579/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree030.table
  base := (-9918773167503823822106923239302505577721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-14689660637653623013743065035600000000000000)
      constant := (131245938734197936792976813056408974549385591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree030.table
  base := (-9919553718685300222686811830328511116451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-38158298895484561600865980486000000000000000)
      constant := (342335843773712510592112350182280268281578581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266788382254120345157/100000000000000000000)
  centralHi := (133394191127060172579/50000000000000000000)
  directionLo := (271349197794835312857/100000000000000000000)
  directionHi := (135674598897417656429/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree031.table
  base := (-4998849306234457994065694916679071121761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-7566166160251541541459374716820000000000000)
      constant := (69816070852732192597451061071686771376588431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree031.table
  base := (-9998322395885063173596682184813142562453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-39308653067972957834141922884920000000000000)
      constant := (364211874201012628465494656191170807832001843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271349197794835312857/100000000000000000000)
  centralHi := (135674598897417656429/50000000000000000000)
  directionLo := (275834612371309702043/100000000000000000000)
  directionHi := (68958653092827425511/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree032.table
  base := (-10035729592539840358376770625098093750373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-15575004003352543152094433831680000000000000)
      constant := (148290183582444325791198215323003108406052683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree032.table
  base := (-8028982070279348480191124784175188843/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-20229503620230677033708932641920000000000000)
      constant := (193398375229560389660986101255900104046208125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275834612371309702043/100000000000000000000)
  centralHi := (68958653092827425511/25000000000000000000)
  directionLo := (35031030802204649897/12500000000000000000)
  directionHi := (280248246417637199177/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree033.table
  base := (-2006623639449870575054651607272596631119/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-16017675686202003221270118229720000000000000)
      constant := (157219931009774930688319520804143981910690245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree033.table
  base := (-10033515389030088401770667287223536565343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-41609361412949750300693807682760000000000000)
      constant := (410090135644731598950598804151410978442045433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35031030802204649897/12500000000000000000)
  centralHi := (280248246417637199177/100000000000000000000)
  directionLo := (284593439591095850607/100000000000000000000)
  directionHi := (17787089974443490663/6250000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree034.table
  base := (-4995029739099952703154279383608664726071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-8230173684525731645222901313880000000000000)
      constant := (83210640402579251424182520871231016359908441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree034.table
  base := (-1248796998017814579913083685905210484751/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-10689928896359536633492437520420000000000000)
      constant := (108522942348742650340677792545211533692751762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284593439591095850607/100000000000000000000)
  centralHi := (17787089974443490663/6250000000000000000)
  directionLo := (72218320085877770069/25000000000000000000)
  directionHi := (288873280343511080277/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree035.table
  base := (-9906704366925376776829230708922264284869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-16903019051900923359621487025800000000000000)
      constant := (175894153125813620372726449013480122193304299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree035.table
  base := (-396278254469725859336815104114474926317/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-43910069757926542767245692480600000000000000)
      constant := (458801450482503696880786012984182095646800675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72218320085877770069/25000000000000000000)
  centralHi := (288873280343511080277/100000000000000000000)
  directionLo := (293090631604885602121/100000000000000000000)
  directionHi := (146545315802442801061/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree036.table
  base := (-4891584831019150677243861116116063416637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-8672845367375191714398585711920000000000000)
      constant := (92819243092637126290457798714534602452599027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree036.table
  base := (-1956674026418381777913594215985467702097/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-45060423930414939000521634879520000000000000)
      constant := (484219023374885040026812036900059473579146035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293090631604885602121/100000000000000000000)
  centralHi := (146545315802442801061/50000000000000000000)
  directionLo := (4644502393536324331/1562500000000000000)
  directionHi := (59449630637264951437/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree037.table
  base := (-4809772876422245689589588984377366649367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-8894181208799921748986427910940000000000000)
      constant := (97827116083798812399013977739554373042484857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree037.table
  base := (-1923941022191948275251128916938237713527/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (1092)
      previous := (0)
      next := (832)
      square := (27389385059247529363712914260000000000000)
      linear := (-1248939948727117168481015602120000000000000)
      constant := (13793091023035789657782473606226426022997505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4644502393536324331/1562500000000000000)
  centralHi := (59449630637264951437/20000000000000000000)
  directionLo := (75337080350088399717/25000000000000000000)
  directionHi := (301348321400353598869/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree038.table
  base := (-9415902593694134065848042555685554479167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-18231034100449303567148540219920000000000000)
      constant := (205941354066932487987357911950522341680520657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree038.table
  base := (-9416029178899968340301509353235100937903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-47361132275391731467073519677360000000000000)
      constant := (537177390986343727714960478292941146816010793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75337080350088399717/25000000000000000000)
  centralHi := (301348321400353598869/100000000000000000000)
  directionLo := (305393446309741284737/100000000000000000000)
  directionHi := (152696723154870642369/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree039.table
  base := (-4586147162966848924896753089476190484279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-9336852891649381818162112308980000000000000)
      constant := (108249911621253280173316097617477095233816409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree039.table
  base := (-9172394808771420558988583388980215781253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-48511486447880127700349462076280000000000000)
      constant := (564718020941599831823738449841066084595464643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305393446309741284737/100000000000000000000)
  centralHi := (152696723154870642369/50000000000000000000)
  directionLo := (151067229954119349/48828125000000000)
  directionHi := (309385686946036426753/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree040.table
  base := (-444438142698748203888132304742211928467/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-4779094366537055926374977254000000000000000)
      constant := (56832404381721502385855400365956849449204785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree040.table
  base := (-277776330142240369095420524251967025557/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-12415460155092130983406351118800000000000000)
      constant := (148241550546501800945298761562392457136099736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151067229954119349/48828125000000000)
  centralHi := (309385686946036426753/100000000000000000000)
  directionLo := (313327064782474347539/100000000000000000000)
  directionHi := (15666353239123717377/5000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree041.table
  base := (-4282670306178540488973837037851001761001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-9779524574498841887337796707020000000000000)
      constant := (119215359881099813082506225304786820068430471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree041.table
  base := (-535337737835388270044617701198020915691/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-12703048698214230041725336718530000000000000)
      constant := (155480472947230782402594040674184637465676084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313327064782474347539/100000000000000000000)
  centralHi := (15666353239123717377/5000000000000000000)
  directionLo := (317219475699918050391/100000000000000000000)
  directionHi := (39652434462489756299/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree042.table
  base := (-1025256588366991078674381523738324125521/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-5000430207961785960962819453020000000000000)
      constant := (62450779166862412412397291059504853075198782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree042.table
  base := (-4101051387689644615755542642120112175749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-25981274482672658200088644636520000000000000)
      constant := (325792528280043336415886932744897566431399619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317219475699918050391/100000000000000000000)
  centralHi := (39652434462489756299/12500000000000000000)
  directionLo := (32106470064686482189/10000000000000000000)
  directionHi := (321064700646864821891/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree043.table
  base := (-7798918571828160328016441782968278287771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-20444392514696603913026962210120000000000000)
      constant := (261446797961988370403614473497389780785769141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree043.table
  base := (-1559791643817516896455088903334863774929/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-53112903137833712633453231671960000000000000)
      constant := (681955670838281903251129362293092857460610995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32106470064686482189/10000000000000000000)
  centralHi := (321064700646864821891/100000000000000000000)
  directionLo := (81216103790901185371/25000000000000000000)
  directionHi := (64972883032720948297/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree044.table
  base := (-3677976625830403187028277111764926620519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-10443532098773031991101323304080000000000000)
      constant := (136680877843604044699129463036836353817745449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree044.table
  base := (-7355984629825510028916525671397354217799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-54263257310322108866729174070880000000000000)
      constant := (713033714782134010900802458957137022075833169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81216103790901185371/25000000000000000000)
  centralHi := (64972883032720948297/20000000000000000000)
  directionLo := (328620197915041375819/100000000000000000000)
  directionHi := (16431009895752068791/5000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree045.table
  base := (-6873168393878294140881954418784918911711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-21329735880395524051378331006200000000000000)
      constant := (285547983681610704553011609130962777895704881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree045.table
  base := (-3436596607394049783998399432810414661519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-27706805741405252550002558234900000000000000)
      constant := (372409586524496497325099566945732542328380489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (328620197915041375819/100000000000000000000)
  centralHi := (16431009895752068791/5000000000000000000)
  directionLo := (6646670767108928681/2000000000000000000)
  directionHi := (332333538355446434051/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree046.table
  base := (-1587643254170091601461197412667956235607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57500000000000000000000000000000000000000
      center := (169)
      previous := (0)
      next := (130)
      square := (4256458488937116049766196135000000000000)
      linear := (-236656603948315044788630602220000000000000)
      constant := (3239189969288788608028839529968637006581039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree046.table
  base := (-6350592640948777947843672950045397164741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-56563965655298901333281058868720000000000000)
      constant := (777312033773772235881959164379467851281469571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6646670767108928681/2000000000000000000)
  centralHi := (332333538355446434051/100000000000000000000)
  directionLo := (67201168726140770307/20000000000000000000)
  directionHi := (21000365226918990721/6250000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree047.table
  base := (-1447043525832408463863810207063449619749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-5553769811523611047432424950570000000000000)
      constant := (77683558117983927625504980812808435151152779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree047.table
  base := (-723523701453184957501674002397610858217/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-14428579956946824391639250316910000000000000)
      constant := (202628071944907370569285513063940341470201854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67201168726140770307/20000000000000000000)
  centralHi := (21000365226918990721/6250000000000000000)
  directionLo := (339638444808756934027/100000000000000000000)
  directionHi := (84909611202189233507/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree048.table
  base := (-1037195412418179761829821014751475397963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-22657750928943904258905384200320000000000000)
      constant := (323734246712740099816130131935662347572387865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree048.table
  base := (-5185989312148455306809307431647690039061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-58864674000275693799832943666560000000000000)
      constant := (844419927967847620761194509510394312336525491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339638444808756934027/100000000000000000000)
  centralHi := (84909611202189233507/25000000000000000000)
  directionLo := (85808150629121856989/25000000000000000000)
  directionHi := (343232602516487427957/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree049.table
  base := (-2271993041092407118513949285636817963037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-11550211305896682164040534299180000000000000)
      constant := (168502758840441997229900080374508123297553427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree049.table
  base := (-4543995754350522748788484667462621200803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-60015028172764090033108886065480000000000000)
      constant := (879034948846227523683013913501223671576100693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85808150629121856989/25000000000000000000)
  centralHi := (343232602516487427957/100000000000000000000)
  directionLo := (173394756025356108357/50000000000000000000)
  directionHi := (69357902410142443343/20000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree050.table
  base := (-482775551158463094147307953712442406819/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-5885773573660706099314188249100000000000000)
      constant := (87637010914853799678044517527472235933585498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree050.table
  base := (-3862212042851626753914466027165427025023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-61165382345252486266384828464400000000000000)
      constant := (914357346164544486655258174818810530402743513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173394756025356108357/50000000000000000000)
  centralHi := (69357902410142443343/20000000000000000000)
  directionLo := (350310308022046498971/100000000000000000000)
  directionHi := (87577577005511624743/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree051.table
  base := (-628126911726546606987306662245734657629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-23985765977492284466432437394440000000000000)
      constant := (364361823317743629516953257228380031830571295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree051.table
  base := (-628128116178699979949831129303878545273/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-62315736517740882499660770863320000000000000)
      constant := (950387116632760577779245046701294951357606315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (350310308022046498971/100000000000000000000)
  centralHi := (87577577005511624743/25000000000000000000)
  directionLo := (353796068582779926859/100000000000000000000)
  directionHi := (17689803429138996343/5000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree052.table
  base := (-237927848021337175104034213417105249697/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-12214218830170872267804060896240000000000000)
      constant := (189223427812177239916181598022151756614551435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree052.table
  base := (-297410403681086577056961994361367570563/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-15866522672557319683234178315560000000000000)
      constant := (246781064425801093879020296790718575591798506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353796068582779926859/100000000000000000000)
  centralHi := (17689803429138996343/5000000000000000000)
  directionLo := (357247819283422833769/100000000000000000000)
  directionHi := (35724781928342283377/10000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree053.table
  base := (-789068843143156389501150202854181863383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-12435554671595602302391903095260000000000000)
      constant := (196401569889626689827601910752580137794270393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree053.table
  base := (-789070715106090668916812520110761890107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-32308222431358837483106327830580000000000000)
      constant := (512284383701097728563947514280578366972443517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357247819283422833769/100000000000000000000)
  centralHi := (35724781928342283377/10000000000000000000)
  directionLo := (360666536597022210393/100000000000000000000)
  directionHi := (180333268298511105197/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree054.table
  base := (-737213350307065939970476023194493140099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-25313781026040664673959490588560000000000000)
      constant := (407430675161682364290087805693250113128887629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree054.table
  base := (-36860815033762437821122985597297760301/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-16441699758801517799872149515020000000000000)
      constant := (265680161049972064152149993096006496830739655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360666536597022210393/100000000000000000000)
  centralHi := (180333268298511105197/50000000000000000000)
  directionLo := (182026575572786337677/50000000000000000000)
  directionHi := (72810630229114535071/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree055.table
  base := (8968351037203497327518987827840914833/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-6439113177222531185783793746650000000000000)
      constant := (105582365322413533265288026253868711375786628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree055.table
  base := (143491292380320622412403555773972819189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-66917153207694467432764540459000000000000000)
      constant := (1101579886909658510970350790858354568789469741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182026575572786337677/50000000000000000000)
  centralHi := (72810630229114535071/20000000000000000000)
  directionLo := (14696342026349343521/4000000000000000000)
  directionHi := (183704275329366794013/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree056.table
  base := (1063982506413088937712477249362110136921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-26199124391739584812310859384640000000000000)
      constant := (437499497788632684625665329263632556262431209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree056.table
  base := (531990338034326551828144160837525192999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-34033753690091431833020241428960000000000000)
      constant := (570573247305162729562336195968026571989215631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14696342026349343521/4000000000000000000)
  centralHi := (183704275329366794013/50000000000000000000)
  directionLo := (370733582691508036483/100000000000000000000)
  directionHi := (92683395672877009121/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree057.table
  base := (2024252768436605474824124817959083901257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-26641796074589044881486543782680000000000000)
      constant := (452940784367292520222044483026880355383764953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree057.table
  base := (506062831869997193989951786131820970873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-17304465388167814974829106314210000000000000)
      constant := (295355116646506409938231866052519462909125137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370733582691508036483/100000000000000000000)
  centralHi := (92683395672877009121/25000000000000000000)
  directionLo := (18701452856222912253/5000000000000000000)
  directionHi := (374029057124458245061/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree058.table
  base := (3024303973785810875219132072958337594937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-27084467757438504950662228180720000000000000)
      constant := (468653320798756122657504181767474960587721673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree058.table
  base := (94509463741487131763168256676678531443/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-17592053931289914033148091913940000000000000)
      constant := (305600450569932776646290937598902983276363736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18701452856222912253/5000000000000000000)
  centralHi := (374029057124458245061/100000000000000000000)
  directionLo := (188647874233677273499/50000000000000000000)
  directionHi := (377295748467354546999/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree059.table
  base := (4064135787957375636852889861660343108263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-27527139440287965019837912578760000000000000)
      constant := (484637106906071230625462827243638321504271127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree059.table
  base := (2032067447849397948144367822692699363183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-35759284948824026182934155027340000000000000)
      constant := (632045250628657317101259686927956305428197527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188647874233677273499/50000000000000000000)
  centralHi := (377295748467354546999/100000000000000000000)
  directionLo := (190267198992411256941/50000000000000000000)
  directionHi := (380534397984822513883/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree060.table
  base := (2571873974787172783281902182394811409389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-13984905561568712544506798488400000000000000)
      constant := (250446071275484717678868968162486855235566781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree060.table
  base := (2571873623880689114412053814845786044921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-36334462035068224299572126226800000000000000)
      constant := (653243281589883847412375174812523881095496849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190267198992411256941/50000000000000000000)
  centralHi := (380534397984822513883/100000000000000000000)
  directionLo := (383745715660515635193/100000000000000000000)
  directionHi := (191872857830257817597/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree061.table
  base := (3131570126968255294107135644584123753559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-14206241402993442579094640687420000000000000)
      constant := (258709213812582162862026358170195001465632711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree061.table
  base := (6263139702073299203011236176487943144203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-73819278242624844832420194852520000000000000)
      constant := (1349589987781720541152775412300591994164413907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383745715660515635193/100000000000000000000)
  centralHi := (191872857830257817597/50000000000000000000)
  directionLo := (386930382014557415579/100000000000000000000)
  directionHi := (19346519100727870779/5000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree062.table
  base := (2899340836049310681419663573934278173/3906250000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-7213788622209086306841241443220000000000000)
      constant := (133553990510903778155089615685611189218250880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree062.table
  base := (1855578026612749696490129900418161992243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-18742408103778310266424034312860000000000000)
      constant := (348350193713708469875392174294252463767380667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386930382014557415579/100000000000000000000)
  centralHi := (19346519100727870779/5000000000000000000)
  directionLo := (24380565611714480531/6250000000000000000)
  directionHi := (390089049787431688497/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree063.table
  base := (2155316170487475080135882772666768427369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-7324456542921451324135162542730000000000000)
      constant := (137821186434827862830847300977485720498078201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree063.table
  base := (8621264340988464484836905014789248411149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-76119986587601637298972079650360000000000000)
      constant := (1437918924234956378768439016847266481074862981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24380565611714480531/6250000000000000000)
  centralHi := (390089049787431688497/100000000000000000000)
  directionLo := (78644469100424698733/20000000000000000000)
  directionHi := (196611172751061746833/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree064.table
  base := (1971999315740995414360898048130211026151/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-29740497854535265365716334568960000000000000)
      constant := (568624778659235624285878877422424408164169395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree064.table
  base := (9859996310802753821146801602723585445163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-77270340760090033532248022049280000000000000)
      constant := (1483144435792193290700328645488208588474428147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78644469100424698733/20000000000000000000)
  centralHi := (196611172751061746833/50000000000000000000)
  directionLo := (79266174183019935249/20000000000000000000)
  directionHi := (198165435457549838123/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree065.table
  base := (11138508150869706883692386353684869511817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-30183169537384725434892018967000000000000000)
      constant := (586236060761235981147843848291599295971751193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree065.table
  base := (5569253970211681305480670941750777176543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-39210347466289214882761982224100000000000000)
      constant := (764538654711612747534719481758506813954687367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79266174183019935249/20000000000000000000)
  centralHi := (198165435457549838123/50000000000000000000)
  directionLo := (199707602182823416171/50000000000000000000)
  directionHi := (399415204365646832343/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree066.table
  base := (12456799334726074873154683512174838132317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-30625841220234185504067703365040000000000000)
      constant := (604118592011605692036149325017060489371995693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree066.table
  base := (12456799169452392366984478861129712532009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-79571049105066825998799906847120000000000000)
      constant := (1575717545045368268846661682596166576456320321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199707602182823416171/50000000000000000000)
  centralHi := (399415204365646832343/100000000000000000000)
  directionLo := (100618975508033972401/25000000000000000000)
  directionHi := (80495180406427177921/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree067.table
  base := (6907435039487391342481334380005495562721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-15534256451541822786621693881540000000000000)
      constant := (311136186191603714060439659222512907152679409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree067.table
  base := (3453717487301788878518343492772080834127/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-20180350819388805558018962311510000000000000)
      constant := (405766285647993753185406564182709978661919863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100618975508033972401/25000000000000000000)
  centralHi := (80495180406427177921/20000000000000000000)
  directionLo := (405513499102941662139/100000000000000000000)
  directionHi := (20275674955147083107/5000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree068.table
  base := (7606360170994517882857011569733699698153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-15755592292966552821209536080560000000000000)
      constant := (320348700927010307541642000923429127140322937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree068.table
  base := (15212720240122316464755065280927343700589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-81871757450043618465351791644960000000000000)
      constant := (1671120102008880782335082201035509533526106341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405513499102941662139/100000000000000000000)
  centralHi := (20275674955147083107/5000000000000000000)
  directionLo := (8170570217379971581/2000000000000000000)
  directionHi := (408528510868998579051/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree069.table
  base := (8325175044843337292729490085868038873317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115000000000000000000000000000000000000000
      center := (338)
      previous := (0)
      next := (260)
      square := (8512916977874232099532392270000000000000)
      linear := (-694649049321360124165103403460000000000000)
      constant := (14334645226217734576783042364244964894086291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree069.table
  base := (16650350009739264888808259382647724303999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-83022111622532014698627734043880000000000000)
      constant := (1719882423251649740084956564834624734572174631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8170570217379971581/2000000000000000000)
  centralHi := (408528510868998579051/100000000000000000000)
  directionLo := (411521433744308769087/100000000000000000000)
  directionHi := (6430022402254824517/1562500000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree070.table
  base := (18127759293880974828405658404109843861097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-32396527951632025780770440957200000000000000)
      constant := (678361208024282177304033253881774107402520313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree070.table
  base := (18127759231149528688234087505357625082721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-84172465795020410931903676442800000000000000)
      constant := (1769352106283444187689088896780834588738245049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411521433744308769087/100000000000000000000)
  centralHi := (6430022402254824517/1562500000000000000)
  directionLo := (10362318655503142687/2500000000000000000)
  directionHi := (414492746220125707481/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree071.table
  base := (3928989586200402800182947756672461458399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-32839199634481485849946125355240000000000000)
      constant := (697599984696351286400188717447218660557465355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree071.table
  base := (9822473940894633103950348961536068711031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-42661409983754403582589809420860000000000000)
      constant := (909764575536687112960801845930632878065401439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10362318655503142687/2500000000000000000)
  centralHi := (414492746220125707481/100000000000000000000)
  directionLo := (417442909758006976117/100000000000000000000)
  directionHi := (208721454879003488059/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree072.table
  base := (848076639244197456190345648589254233279/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-33281871317330945919121809753280000000000000)
      constant := (717110010411672289156123949581472887235114775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree072.table
  base := (5300478985626311482385470943023336823609/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-21618293534999300849613890310160000000000000)
      constant := (467603389398804770208498628219878948111520721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417442909758006976117/100000000000000000000)
  centralHi := (208721454879003488059/50000000000000000000)
  directionLo := (84074473925291159753/20000000000000000000)
  directionHi := (210186184813227899383/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree073.table
  base := (2849832928387544852565444263745769956589/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-8431135750045101497074373537830000000000000)
      constant := (184222821290301225462192260988588024614071162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree073.table
  base := (11399331698415392750150157900427940847307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-43811764156242799815865751819780000000000000)
      constant := (961002662913217932142599838045095851019963283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84074473925291159753/20000000000000000000)
  centralHi := (210186184813227899383/50000000000000000000)
  directionLo := (423281555685446326899/100000000000000000000)
  directionHi := (4232815556854463269/1000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree074.table
  base := (24435190254156794488173107279773708811221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-34167214683029866057473178549360000000000000)
      constant := (756943808937103267982064760735720291961135909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree074.table
  base := (6108797557606021215509248213537180422577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 92500000000000000000000000000000000000000
      center := (273)
      previous := (0)
      next := (208)
      square := (6847346264811882340928228565000000000000)
      linear := (-599823530303878350439239500260000000000000)
      constant := (13339894971266153054024506006160875675635349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423281555685446326899/100000000000000000000)
  centralHi := (4232815556854463269/1000000000000000000)
  directionLo := (213085441561373228897/50000000000000000000)
  directionHi := (85234176624549291559/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree075.table
  base := (5222299289847259925534309572477713263241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-34609886365879326126648862947400000000000000)
      constant := (777267581732470315296372186661703551581272445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree075.table
  base := (6527874107658045363407227216341889946879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-22481059164365598024570847109350000000000000)
      constant := (506827736835190384554774689009797047337277351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213085441561373228897/50000000000000000000)
  centralHi := (85234176624549291559/20000000000000000000)
  directionLo := (214520376572804642473/50000000000000000000)
  directionHi := (429040753145609284947/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree076.table
  base := (13913791000366656422782641300481721874841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-17526279024364393097912273672720000000000000)
      constant := (398931301770583350907277185449714830871790889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree076.table
  base := (2782758198615209857070612541764921462771/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-45537295414975394165779665418160000000000000)
      constant := (1040512400295537373923666415889820887412667495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214520376572804642473/50000000000000000000)
  centralHi := (429040753145609284947/100000000000000000000)
  directionLo := (431891553631095760341/100000000000000000000)
  directionHi := (215945776815547880171/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree077.table
  base := (2958344689819344223139040455301012267869/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-17747614865789123132500115871740000000000000)
      constant := (409364437178831027107987953338161177448513505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree077.table
  base := (14791723443383603611922504094869647553201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-46112472501219592282417636617620000000000000)
      constant := (1067723007742171857896904080373686547500332169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (431891553631095760341/100000000000000000000)
  centralHi := (215945776815547880171/50000000000000000000)
  directionLo := (27170228733625811229/6250000000000000000)
  directionHi := (86944731947602595933/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree078.table
  base := (7844772783023551445348444335521809148227/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-8984475353606926583543979035380000000000000)
      constant := (209966598544229744880162846212311037039412083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree078.table
  base := (31379091123141807190431814342469783585681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-93375299174927580798111215634160000000000000)
      constant := (2190574592007787868453766528995561133728797289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27170228733625811229/6250000000000000000)
  centralHi := (86944731947602595933/20000000000000000000)
  directionLo := (109384358620800336207/25000000000000000000)
  directionHi := (437537434483201344829/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree079.table
  base := (8303628673418448680682574532577933116551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-9095143274319291600837900134890000000000000)
      constant := (215318790748575620221936436504238726618655479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree079.table
  base := (1660725734333039337340224716425742154547/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-23631413336853994257846789508270000000000000)
      constant := (561602632537403279469378647673479205047874215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109384358620800336207/25000000000000000000)
  centralHi := (437537434483201344829/100000000000000000000)
  directionLo := (440333229284676778401/100000000000000000000)
  directionHi := (220166614642338389201/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree080.table
  base := (17544858787398537341624497767361048275243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-18411622390063313236263642468800000000000000)
      constant := (441477590402754536117195563158933994537603547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree080.table
  base := (35089717569304199683450731618914819629721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-95676007519904373264663100432000000000000000)
      constant := (2302953829898840157704229984514294388073088049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440333229284676778401/100000000000000000000)
  centralHi := (220166614642338389201/50000000000000000000)
  directionLo := (443111384473928578733/100000000000000000000)
  directionHi := (221555692236964289367/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree081.table
  base := (37004699767850474126298001035832815265703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-37265916462976086541702969335640000000000000)
      constant := (904906447606511174217698687305175559275556887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree081.table
  base := (1480187990541956048513554077296104130057/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-96826361692392769497939042830920000000000000)
      constant := (2360204491245169802719781848365639163851200825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443111384473928578733/100000000000000000000)
  centralHi := (221555692236964289367/50000000000000000000)
  directionLo := (13933507180608972993/3125000000000000000)
  directionHi := (445872229779487135777/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree082.table
  base := (9739865316414823440341133076507611629027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-9427147036456386652719663433420000000000000)
      constant := (231782240848378342728246791781892526551755283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree082.table
  base := (779189225245823295241807111214905103511/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-48988357932440582865607492614920000000000000)
      constant := (1209081257089438525622949758073690127167663975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13933507180608972993/3125000000000000000)
  centralHi := (445872229779487135777/100000000000000000000)
  directionLo := (224308042391853282459/50000000000000000000)
  directionHi := (448616084783706564919/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree083.table
  base := (40954002061422429128581920541324201459571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-38151259828675006680054338131720000000000000)
      constant := (949622728162917878060987097987740502572113059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree083.table
  base := (40954002058785578040612647395952551846273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-99127070037369561964490927628760000000000000)
      constant := (2476827898690727433856761725156679043477547737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224308042391853282459/50000000000000000000)
  centralHi := (448616084783706564919/100000000000000000000)
  directionLo := (451343259354553581269/100000000000000000000)
  directionHi := (45134325935455358127/10000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree084.table
  base := (10747080537165156874089738881579510191991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-9648482877881116687307505632440000000000000)
      constant := (243096935477824292741671682420435560891563239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree084.table
  base := (21494161073298290445445712976362098033147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-50138712104928979098883435013840000000000000)
      constant := (1268100322385955334348365698330079712207378243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451343259354553581269/100000000000000000000)
  centralHi := (45134325935455358127/10000000000000000000)
  directionLo := (227027027027027027027/50000000000000000000)
  directionHi := (90810810810810810811/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree085.table
  base := (4506242152117527410209747996747722264881/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-19518301597186963409202853463900000000000000)
      constant := (497712002317686091210335818500647725390610245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree085.table
  base := (45062421519559830154301476745492580831777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-101427778382346354431042812426600000000000000)
      constant := (2596280752413987769981650612027079343158702713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227027027027027027027/50000000000000000000)
  centralHi := (90810810810810810811/20000000000000000000)
  directionLo := (114187190131230313137/25000000000000000000)
  directionHi := (456748760524921252549/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree086.table
  base := (5897037521626922407421516538697577353571/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-9869818719305846721895347831460000000000000)
      constant := (254682879082998709719705700920922036840078118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree086.table
  base := (2358815008587560645285443440802243706499/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-25644533138708687666079688706380000000000000)
      constant := (664267055402212156779252754943911358170985655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114187190131230313137/25000000000000000000)
  centralHi := (456748760524921252549/100000000000000000000)
  directionLo := (459427661856773579043/100000000000000000000)
  directionHi := (114856915464193394761/25000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree087.table
  base := (4932995809845096156989213838036308080363/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-19960973280036423478378537861940000000000000)
      constant := (521155138499066990090722205095896034872560135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree087.table
  base := (6166244762182727660540507431691227049207/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-25932121681830786724398674306110000000000000)
      constant := (679640763087169436310347933983675579660728766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (459427661856773579043/100000000000000000000)
  centralHi := (114856915464193394761/25000000000000000000)
  directionLo := (231045516466621737873/50000000000000000000)
  directionHi := (462091032933243475747/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree088.table
  base := (25761697645975713973259477733098941915911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-20182309121461153512966380060960000000000000)
      constant := (533080143315431961292720083715049340273516919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree088.table
  base := (51523395291177582512207577387594681482497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-104878840899811543130870639623360000000000000)
      constant := (2780765244625926358721793624335137118949538393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231045516466621737873/50000000000000000000)
  centralHi := (462091032933243475747/100000000000000000000)
  directionLo := (464739140761182206253/100000000000000000000)
  directionHi := (232369570380591103127/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree089.table
  base := (13439152937041966274831133737874196985369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-10201822481442941773777111129990000000000000)
      constant := (272570386306838772740109534420240450205260201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree089.table
  base := (26878305873781265926189569180601265283659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-53014597536149969682073291011140000000000000)
      constant := (1421837399216644765916645337914533132173329171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464739140761182206253/100000000000000000000)
  centralHi := (232369570380591103127/50000000000000000000)
  directionLo := (467372244783076469679/100000000000000000000)
  directionHi := (5842153059788455871/1250000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree090.table
  base := (28014803730959200121607869584845312643527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-20624980804310613582142064459000000000000000)
      constant := (557337026392433137301562025559383170388425783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree090.table
  base := (7003700932680617972149954845879397332887/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-26794887311197083899355631105300000000000000)
      constant := (726822928440921793082136239394517789897444606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467372244783076469679/100000000000000000000)
  centralHi := (5842153059788455871/1250000000000000000)
  directionLo := (469990597173711521309/100000000000000000000)
  directionHi := (46999059717371152131/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree091.table
  base := (29171191214087988530182101945633348140633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-20846316645735343616729906658020000000000000)
      constant := (569668904650369080360683351533050041166394857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree091.table
  base := (5834238242780571261558319110171644055139/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-54164951708638365915349233410060000000000000)
      constant := (1485807995305124062271919944795014903557426455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469990597173711521309/100000000000000000000)
  centralHi := (46999059717371152131/10000000000000000000)
  directionLo := (472594443122040945307/100000000000000000000)
  directionHi := (118148610780510236327/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree092.table
  base := (3034746832102901939115841964701805049859/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57500000000000000000000000000000000000000
      center := (169)
      previous := (0)
      next := (130)
      square := (4256458488937116049766196135000000000000)
      linear := (-457992445373045079376472801240000000000000)
      constant := (12655139291004216052007113141380707580733785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree092.table
  base := (60694936641768510113233109244288433462637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-109480257589765128063974409219040000000000000)
      constant := (3036647628966296695099043308565350865410350053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (472594443122040945307/100000000000000000000)
  centralHi := (118148610780510236327/25000000000000000000)
  directionLo := (237592010549577411537/50000000000000000000)
  directionHi := (19007360843966192923/4000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree093.table
  base := (63087270098817723233479650917801404603849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-42577976657169607371811182112120000000000000)
      constant := (1189479069197304332702097945872096943035436121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree093.table
  base := (12617454019718270541776375012979405108297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-110630611762253524297250351617960000000000000)
      constant := (3102386628825341108498779982184264027966292965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237592010549577411537/50000000000000000000)
  centralHi := (19007360843966192923/4000000000000000000)
  directionLo := (238879781556587600409/50000000000000000000)
  directionHi := (477759563113175200819/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree094.table
  base := (8189922849229532777573743745840356856591/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-10755162085004766860246716627540000000000000)
      constant := (303739143143261050024865337822079097554273278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree094.table
  base := (32759691396829646443007449424478358901761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-55890482967370960265263147008440000000000000)
      constant := (1584416495090531750796470718563750873336510809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238879781556587600409/50000000000000000000)
  centralHi := (477759563113175200819/100000000000000000000)
  directionLo := (120080323737962493651/25000000000000000000)
  directionHi := (96064258990369994921/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree095.table
  base := (4249454670163521594086809801337396705739/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-10865830005717131877540637727050000000000000)
      constant := (310176331224307100465176432709254931429343724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree095.table
  base := (8498909340309751512883907135024929914319/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-28232830026807579190950559103950000000000000)
      constant := (808996678256827788074532692275323258105405422) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120080323737962493651/25000000000000000000)
  centralHi := (96064258990369994921/20000000000000000000)
  directionLo := (96573887282712624959/20000000000000000000)
  directionHi := (120717359103390781199/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree096.table
  base := (70502945880776262205416908839513023729779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-43905991705717987579338235306240000000000000)
      constant := (1266725326167539012929009870080422389553053091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree096.table
  base := (70502945880668141709570195061714387721679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-114081674279718712997078178814720000000000000)
      constant := (3303847797358088704931839824925566996790978551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96573887282712624959/20000000000000000000)
  centralHi := (120717359103390781199/25000000000000000000)
  directionLo := (97080840305486046761/20000000000000000000)
  directionHi := (242702100763715116903/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree097.table
  base := (73054396264044673271444219589953257603349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-44348663388567447648513919704280000000000000)
      constant := (1293016576381716494947331317796465273272171621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree097.table
  base := (36527198131980088073865047683256234434973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-57616014226103554615177060606820000000000000)
      constant := (1686208121583775603192732785171387784941478037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97080840305486046761/20000000000000000000)
  centralHi := (242702100763715116903/50000000000000000000)
  directionLo := (243962899381551520799/50000000000000000000)
  directionHi := (487925798763103041599/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree098.table
  base := (75645625868255900352755694497005871309593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-44791335071416907717689604102320000000000000)
      constant := (1319579075537557204068141736054596105922774697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree098.table
  base := (75645625868189872113470584939665788916917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-116382382624695505463630063612560000000000000)
      constant := (3441692050449997807575721974640722465027259373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243962899381551520799/50000000000000000000)
  centralHi := (487925798763103041599/100000000000000000000)
  directionLo := (490434431230865098559/100000000000000000000)
  directionHi := (1532607597596453433/312500000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree099.table
  base := (15655326937869128188955718987309887204943/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-45234006754266367786865288500360000000000000)
      constant := (1346412823632911124266522146122654651657074235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree099.table
  base := (78276634689294050135783845291863242299069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-117532736797183901696906006011480000000000000)
      constant := (3511675219199866015806799334307540778707425461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490434431230865098559/100000000000000000000)
  centralHi := (1532607597596453433/312500000000000000)
  directionLo := (492930296872562063729/100000000000000000000)
  directionHi := (49293029687256206373/10000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree100.table
  base := (2023685568083675970327783033569081067993/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-11419169609278956964010243224600000000000000)
      constant := (343379455166419947148618525457580438849682970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree100.table
  base := (80947422723306732720390493015655053057167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-118683090969672297930181948410400000000000000)
      constant := (3582365749411726407889029173458431767635261623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492930296872562063729/100000000000000000000)
  centralHi := (49293029687256206373/10000000000000000000)
  directionLo := (247706794321937297653/50000000000000000000)
  directionHi := (495413588643874595307/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree101.table
  base := (4182899498319352676956497705834050100977/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-11529837529991321981304164324110000000000000)
      constant := (350223516658453589667636387427436062517084165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree101.table
  base := (20914497491588891736305798961903220775447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-29958361285540173540864472702330000000000000)
      constant := (913440910270069433168025328556190509241586943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247706794321937297653/50000000000000000000)
  centralHi := (495413588643874595307/100000000000000000000)
  directionLo := (99576898937681768579/20000000000000000000)
  directionHi := (31117780918025552681/6250000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree102.table
  base := (43204168207341542295650748272027655826991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-23281010901407373997196170847240000000000000)
      constant := (714270780767656919406777767249542629932478239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree102.table
  base := (86408336414658490083032945057371531623531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-120983799314649090396733833208240000000000000)
      constant := (3725868894200342346282411863654661626792613939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99576898937681768579/20000000000000000000)
  centralHi := (31117780918025552681/6250000000000000000)
  directionLo := (500343198504049053699/100000000000000000000)
  directionHi := (5003431985040490537/1000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree103.table
  base := (17839692412907962866693766749375307741431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-47004693485664208063568026092520000000000000)
      constant := (1456460305368223405993976942427877688976084995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree103.table
  base := (89198462064520605149616109087083004794689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-122134153487137486630009775607160000000000000)
      constant := (3798681508766861934748586050145436633563929241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (500343198504049053699/100000000000000000000)
  centralHi := (5003431985040490537/1000000000000000000)
  directionLo := (502789879101988544713/100000000000000000000)
  directionHi := (251394939550994272357/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree104.table
  base := (46014183456173120704957478094733957624773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-23723682584256834066371855245280000000000000)
      constant := (742325149065316420247317737725874263583504917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree104.table
  base := (18405673382466247953580083469209837668393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-123284507659625882863285718006080000000000000)
      constant := (3872201484774893487586411935258421338840150085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502789879101988544713/100000000000000000000)
  centralHi := (251394939550994272357/50000000000000000000)
  directionLo := (252612355579414542933/50000000000000000000)
  directionHi := (505224711158829085867/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree105.table
  base := (94898050954572881440830283839228180774787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-47890036851363128201919394888600000000000000)
      constant := (1513111539820675045078611865733451707629862323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree105.table
  base := (94898050954561166810710197040025985433029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-124434861832114279096561660405000000000000000)
      constant := (3946428822219605492858786022938295574057816701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252612355579414542933/50000000000000000000)
  centralHi := (505224711158829085867/100000000000000000000)
  directionLo := (507647865162114417563/100000000000000000000)
  directionHi := (126911966290528604391/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree106.table
  base := (97807514187769116264635911674646088878167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-48332708534212588271095079286640000000000000)
      constant := (1541844030436524642738430872516607781016550343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree106.table
  base := (97807514187759969257381715635378039327331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-125585216004602675329837602803920000000000000)
      constant := (4021363521096274329664419663346512535839116139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507647865162114417563/100000000000000000000)
  centralHi := (126911966290528604391/25000000000000000000)
  directionLo := (255029753774820518913/50000000000000000000)
  directionHi := (510059507549641037827/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree107.table
  base := (3148648644017521135677766119863977156411/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-12193845054265512085067690921170000000000000)
      constant := (392711942494099161221905294369809351325931352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree107.table
  base := (100756756608553534818247987188052496050503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-126735570177091071563113545202840000000000000)
      constant := (4097005581400280838278758752725663867093138607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255029753774820518913/50000000000000000000)
  centralHi := (510059507549641037827/100000000000000000000)
  directionLo := (512459800842868400669/100000000000000000000)
  directionHi := (51245980084286840067/10000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree108.table
  base := (103745778213647243593449805767541886898827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-49218051899911508409446448082720000000000000)
      constant := (1600122758438545183262636024917909658169479483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree108.table
  base := (20749155642728333667455144281020321872887/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-127885924349579467796389487601760000000000000)
      constant := (4173355003127107051533193716664704103219911515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512459800842868400669/100000000000000000000)
  centralHi := (51245980084286840067/10000000000000000000)
  directionLo := (102969780754946228387/20000000000000000000)
  directionHi := (32178056485920696371/6250000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree109.table
  base := (106774578999800164052033550145064944034253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-49660723582760968478622132480760000000000000)
      constant := (1629668995821262299914463598461559355394119837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree109.table
  base := (53387289499897905962283249613644559561121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-64518139261033932014832715000340000000000000)
      constant := (2125205893136166536838226809735769402039174649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102969780754946228387/20000000000000000000)
  centralHi := (32178056485920696371/6250000000000000000)
  directionLo := (517226971412137776391/100000000000000000000)
  directionHi := (64653371426517222049/12500000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree110.table
  base := (10984315896386026136098471532164965858673/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-25051697632805214273898908439400000000000000)
      constant := (829743241061438395275269592655576334696190085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree110.table
  base := (109843158963856864311414183052489683005213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-130186632694556260262941372399600000000000000)
      constant := (4328175930831634095071679758768858376034136597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517226971412137776391/100000000000000000000)
  centralHi := (64653371426517222049/12500000000000000000)
  directionLo := (129898538818355846267/25000000000000000000)
  directionHi := (519594155273423385069/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree111.table
  base := (112951518102735743495192813345248325066993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-50546066948459888616973501276840000000000000)
      constant := (1689575217341753097189579337340056363960439297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree111.table
  base := (112951518102733092149712528506270023511501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (1092)
      previous := (0)
      next := (832)
      square := (27389385059247529363712914260000000000000)
      linear := (-3549648293703909635032900399960000000000000)
      constant := (119098579372993987372035532054271990869925537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129898538818355846267/25000000000000000000)
  centralHi := (519594155273423385069/100000000000000000000)
  directionLo := (130487650860252009623/25000000000000000000)
  directionHi := (521950603441008038493/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree112.table
  base := (116099656413400196130437314226572056430413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-50988738631309348686149185674880000000000000)
      constant := (1719935201476290246654071394183936617851688477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree112.table
  base := (116099656413398126963345797899327001995649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-132487341039533052729493257197440000000000000)
      constant := (4485826304175620288313555956292498665732043481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130487650860252009623/25000000000000000000)
  centralHi := (521950603441008038493/100000000000000000000)
  directionLo := (262148230334748995777/50000000000000000000)
  directionHi := (104859292133899598311/20000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree113.table
  base := (59643786946445328474477409101542093270413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-25715705157079404377662435036460000000000000)
      constant := (875283217262460415938959258684205767340048477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree113.table
  base := (59643786946444521127472609637746820443429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-66818847606010724481384599798180000000000000)
      constant := (2282856266476053057670752860407085397187054301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262148230334748995777/50000000000000000000)
  centralHi := (104859292133899598311/20000000000000000000)
  directionLo := (131657967122363239709/25000000000000000000)
  directionHi := (526631868489452958837/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree114.table
  base := (6125763526915288293071418735970349568593/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-12968520499252067206125138617740000000000000)
      constant := (445367229121527508343468010012421574608928485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree114.table
  base := (30628817634576126479572344297825306124993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-33697012346127461299011285498820000000000000)
      constant := (1161576530781565772548936715457742844085115417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131657967122363239709/25000000000000000000)
  centralHi := (526631868489452958837/100000000000000000000)
  directionLo := (528956965307029961387/100000000000000000000)
  directionHi := (132239241326757490347/25000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree115.table
  base := (25156549269360797338546937585896274967427/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 230000000000000000000000000000000000000000
      center := (676)
      previous := (0)
      next := (520)
      square := (17025833955748464199064784540000000000000)
      linear := (-2274641464341640386681575603000000000000000)
      constant := (78810549885145855587186597335878071621254105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree115.table
  base := (125782746346803003636657402707451868825001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-135938403556998241429321084394200000000000000)
      constant := (4727607074694201179776688509765001608421426369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528956965307029961387/100000000000000000000)
  centralHi := (132239241326757490347/25000000000000000000)
  directionLo := (265635943249851129821/50000000000000000000)
  directionHi := (531271886499702259643/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree116.table
  base := (32272500328900474086424113772805278821873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-13189856340676797240712980816760000000000000)
      constant := (461021906785045584113442705061093992496770817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree116.table
  base := (129090001315601129385453285403001219801437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-137088757729486637662597026793120000000000000)
      constant := (4809615387652109901236658726349988669908167253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265635943249851129821/50000000000000000000)
  centralHi := (531271886499702259643/100000000000000000000)
  directionLo := (106715352901648138063/20000000000000000000)
  directionHi := (133394191127060172579/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree117.table
  base := (132437035441972537845013137921119838259629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-53202097045556649032027607665080000000000000)
      constant := (1875803855830150446979375299855252394439343741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree117.table
  base := (13243703544197193952271433155596841439567/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-69119555950987516947936484596020000000000000)
      constant := (2446165530998128034364905291940270379653836115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106715352901648138063/20000000000000000000)
  centralHi := (133394191127060172579/25000000000000000000)
  directionLo := (535871728925134250653/100000000000000000000)
  directionHi := (267935864462567125327/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree118.table
  base := (16977981090405479248607873108911830379473/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-13411192182101527275300823015780000000000000)
      constant := (476947833356711370310585367747248716541482434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree118.table
  base := (4244495272601355226834931119685087498593/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-34847366518615857532287227897740000000000000)
      constant := (1243938524430745405705253410997771078284590536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535871728925134250653/100000000000000000000)
  centralHi := (267935864462567125327/50000000000000000000)
  directionLo := (269078453289808484541/50000000000000000000)
  directionHi := (538156906579616969083/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree119.table
  base := (13925044115679705861115046665869036554507/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-27043720205627784585189488230580000000000000)
      constant := (970025029964441066550402399327433601686671015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree119.table
  base := (139250441156796694557510924344129604010801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-140539820246951826362424853989880000000000000)
      constant := (5059884494828701538519048586618893427890786569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269078453289808484541/50000000000000000000)
  centralHi := (538156906579616969083/100000000000000000000)
  directionLo := (540432421619458918767/100000000000000000000)
  directionHi := (33777026351216182423/6250000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree120.table
  base := (8919800796254085168311264038267698765123/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-13632528023526257309888665214800000000000000)
      constant := (493145008833725634855942409528974450587000268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree120.table
  base := (35679203185016269686985132338233386104989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-35422543604860055648925199097200000000000000)
      constant := (1286180563327475452051776674435041505577729941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540432421619458918767/100000000000000000000)
  centralHi := (33777026351216182423/6250000000000000000)
  directionLo := (108539679117934125143/20000000000000000000)
  directionHi := (135674598897417656429/25000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree121.table
  base := (146222963470532352765465265227131372340867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-54972783776954489308730345257240000000000000)
      constant := (2005381259643575528066194769807972495968318643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree121.table
  base := (73111481735266065658394538231714069827309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-71420264295964309414488369393860000000000000)
      constant := (2615133686581568748005296586385506561593586021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108539679117934125143/20000000000000000000)
  centralHi := (135674598897417656429/25000000000000000000)
  directionLo := (544954947508262054837/100000000000000000000)
  directionHi := (272477473754131027419/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree122.table
  base := (149768893345730719223524870188847195632357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-55415455459803949377906029655280000000000000)
      constant := (2038453732853595892246992493742780166489516853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree122.table
  base := (18721111668216318315940531390246715579537/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-35997720691104253765563170296660000000000000)
      constant := (1329129963596257715094048818271875507256772306) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544954947508262054837/100000000000000000000)
  centralHi := (272477473754131027419/50000000000000000000)
  directionLo := (5472021939391897883/1000000000000000000)
  directionHi := (547202193939189788301/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree123.table
  base := (9584662647702557020418220031213306744097/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-13964531785663352361770428513330000000000000)
      constant := (517949363740920922538363873092592357070509252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree123.table
  base := (3067092047264815553186635562425244028921/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (20202)
      previous := (0)
      next := (15392)
      square := (506703623596079293228688913810000000000000)
      linear := (-72570618468452705647764311792780000000000000)
      constant := (2701739848486134770921559127965413976889821225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5472021939391897883/1000000000000000000)
  centralHi := (547202193939189788301/100000000000000000000)
  directionLo := (137360062265654726451/25000000000000000000)
  directionHi := (109888049812523781161/20000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree124.table
  base := (78490045260344931900949625410401211060751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-28150399412751434758128699225680000000000000)
      constant := (1052706212986291784334565935013462240651137279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree124.table
  base := (196225113150862198494982216122898335993/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-36572897777348451882201141496120000000000000)
      constant := (1372786725230401203293012221333569564394883400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137360062265654726451/25000000000000000000)
  centralHi := (109888049812523781161/20000000000000000000)
  directionLo := (551669224742619404087/100000000000000000000)
  directionHi := (68958653092827425511/12500000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree125.table
  base := (4016133945393743802193737980990123612353/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1322500000000000000000000000000000000000000
      center := (3887)
      previous := (0)
      next := (2990)
      square := (97898545245553669144622511105000000000000)
      linear := (-14185867627088082396358270712350000000000000)
      constant := (534824661469766027547010449510062753909347370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree125.table
  base := (20080669726968708776931527054291295474067/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (10101)
      previous := (0)
      next := (7696)
      square := (253351811798039646614344456905000000000000)
      linear := (-36860486320470550940520127095850000000000000)
      constant := (1394880366557462472290880647315274567007995446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551669224742619404087/100000000000000000000)
  centralHi := (68958653092827425511/12500000000000000000)
  directionLo := (553889230592410723417/100000000000000000000)
  directionHi := (276944615296205361709/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree126.table
  base := (82175202123068404686104312120068997697163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (7774)
      previous := (0)
      next := (5980)
      square := (195797090491107338289245022210000000000000)
      linear := (-28593071095600894827304383623720000000000000)
      constant := (1086728057340958600768809724154276499781799227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree126.table
  base := (164350404246136745541090250477405400521897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-148592299454370599995356450782320000000000000)
      constant := (5668603392893878293647918032764447993314476993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553889230592410723417/100000000000000000000)
  centralHi := (276944615296205361709/50000000000000000000)
  directionLo := (22244014961490482189/4000000000000000000)
  directionHi := (278050187018631027363/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree127.table
  base := (168095229809610168677964680218276940009603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-57628813874051249723784451645480000000000000)
      constant := (2207884832379957424086866833347248501265079987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree127.table
  base := (168095229809610118915643744484843321325193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-149742653626858996228632393181240000000000000)
      constant := (5758392680910622281266651573131370506894189217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22244014961490482189/4000000000000000000)
  centralHi := (278050187018631027363/50000000000000000000)
  directionLo := (558302760375150557121/100000000000000000000)
  directionHi := (279151380187575278561/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree128.table
  base := (171879834503970749343268973742355334491939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-58071485556900709792960136043520000000000000)
      constant := (2242584798972021464165718883750985971946235731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree128.table
  base := (34375966900794142110258133624062110592653/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-150893007799347392461908335580160000000000000)
      constant := (5848889330277071311790194850831425147006709785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell165.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558302760375150557121/100000000000000000000)
  centralHi := (279151380187575278561/50000000000000000000)
  directionLo := (560496492835274398353/100000000000000000000)
  directionHi := (280248246417637199177/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree129.table
  base := (175704218327060179332216206693055155934237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (15548)
      previous := (0)
      next := (11960)
      square := (391594180982214676578490044420000000000000)
      linear := (-58514157239750169862135820441560000000000000)
      constant := (2277556014456967542967181696814646177489211373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree129.table
  base := (175704218327060149093957805332675173123463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (40404)
      previous := (0)
      next := (30784)
      square := (1013407247192158586457377827620000000000000)
      linear := (-152043361971835788695184277979080000000000000)
      constant := (5940093340990270574834821633090612312006020847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell165.Kernel129
