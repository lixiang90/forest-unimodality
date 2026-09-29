import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell021.Parameters
import ForestUnimodality.BinomialMassData.Q7_17.Batch000_049
import ForestUnimodality.BinomialMassData.Q7_17.Batch050_099
import ForestUnimodality.BinomialMassData.Q64_153.Batch000_049
import ForestUnimodality.BinomialMassData.Q64_153.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree000.table
  base := (1560359145060249068780677811/100000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (18725452748700729121988928650000000000000)
      constant := (1326305273301211708463576139350000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree000.table
  base := (1560359145060249068780677811/100000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (168529074738306562097900357850000000000000)
      constant := (11936747459710905376172185254150000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree001.table
  base := (20282711704858640177989575410976756802939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (27434753632215194418808580080000000000000)
      constant := (1710671682739239810169128466943024328249815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree001.table
  base := (100565000212140082944475486129393587936263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (736445711556158993382759114780000000000000)
      constant := (45793819769793527171442057542671656862744717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24607647839237516117/50000000000000000000)
  directionHi := (9843059135695006447/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree002.table
  base := (66119295684688304359650808185047065231321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (17418601767028930593639302860000000000000)
      constant := (1101434700119053366945633143785800108932457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree002.table
  base := (65039665075206054734616765805603902345251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (461716974682478614178116082460000000000000)
      constant := (29237094824557563756176068271492191176470209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24607647839237516117/50000000000000000000)
  centralHi := (9843059135695006447/20000000000000000000)
  directionLo := (34800469312350682603/50000000000000000000)
  directionHi := (69600938624701365207/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree003.table
  base := (5400320317931237649237605971930113385631/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (3701224950921333384235012820000000000000)
      constant := (353370010098969356835489477536247710222908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree003.table
  base := (2108603139516987555693446396899355604039/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (31164706301466372495578841690000000000000)
      constant := (3100864744769368726740554665976014074179670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34800469312350682603/50000000000000000000)
  centralHi := (69600938624701365207/100000000000000000000)
  directionLo := (17048678524928751263/20000000000000000000)
  directionHi := (21310848156160939079/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree004.table
  base := (28208254183887522224288800248473897768687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-2613701963343597056699251580000000000000)
      constant := (450850859392157874482209575984056262067679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree004.table
  base := (27333701130480979449244420921775908067763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-87740499064882144231169982180000000000000)
      constant := (11773622769748844565702550529175141803103217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17048678524928751263/20000000000000000000)
  centralHi := (21310848156160939079/25000000000000000000)
  directionLo := (24607647839237516117/25000000000000000000)
  directionHi := (98430591356950064469/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree005.table
  base := (4571181013694991086380267533149544973683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-6314926914264930440934264400000000000000)
      constant := (142644613165475198294666941752084529105222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree005.table
  base := (8794358311131508119750215553937124637517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-181234617969281261717906507250000000000000)
      constant := (3697418196840067142441642203257140208620303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24607647839237516117/25000000000000000000)
  centralHi := (98430591356950064469/100000000000000000000)
  directionLo := (55024373334910902729/50000000000000000000)
  directionHi := (110048746669821805459/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree006.table
  base := (11617497946568970159603928068512103690763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-22646005693716124707037806020000000000000)
      constant := (179209059451825904226458478524705762742971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree006.table
  base := (11085596682011537407000976390504628282861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3382)
      previous := (2432)
      next := (0)
      square := (109462231098107026089349958190000000000000)
      linear := (-212399324270747634213485348940000000000000)
      constant := (1539661688167855588783537947107208127277733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55024373334910902729/50000000000000000000)
  centralHi := (110048746669821805459/100000000000000000000)
  directionLo := (30138090488116465833/25000000000000000000)
  directionHi := (120552361952465863333/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree007.table
  base := (7046776350041634555198430367708327149911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-32662157558902388532207083240000000000000)
      constant := (112893767098165010500821318341041561548487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree007.table
  base := (6651471748874017074578345819058730056719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-911926709685923281845099079140000000000000)
      constant := (2907721653787832632484559507267957096034021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30138090488116465833/25000000000000000000)
  centralHi := (120552361952465863333/100000000000000000000)
  directionLo := (130211433065756796023/100000000000000000000)
  directionHi := (16276429133219599503/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree008.table
  base := (3831224037002174085813025033389040857951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-42678309424088652357376360460000000000000)
      constant := (73740650390639396822066019007613694585167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree008.table
  base := (3543354352588536925168148332350727044501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-1186655446559603661049742111460000000000000)
      constant := (1920014912682711375752565907268983713425959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130211433065756796023/100000000000000000000)
  centralHi := (16276429133219599503/12500000000000000000)
  directionLo := (139201877249402730413/100000000000000000000)
  directionHi := (69600938624701365207/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree009.table
  base := (1496905168620567203589417563939601242313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-52694461289274916182545637680000000000000)
      constant := (53692800069138696876601573996973221119321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree009.table
  base := (1290491492750964554411325958145550209913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3382)
      previous := (2432)
      next := (0)
      square := (109462231098107026089349958190000000000000)
      linear := (-487128061144428013418128381260000000000000)
      constant := (479929738000902074184608477356269182116689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139201877249402730413/100000000000000000000)
  centralHi := (69600938624701365207/50000000000000000000)
  directionLo := (73822943517712548351/50000000000000000000)
  directionHi := (147645887035425096703/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree010.table
  base := (-64807897264397684137203225952456760177/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-31355306577230590003857457450000000000000)
      constant := (23799171728219015849064414317616470153982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree010.table
  base := (-405450535460685208852249386703504124561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-1736112920306964419459028176100000000000000)
      constant := (1330109387234525979325839291503091606826501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73822943517712548351/50000000000000000000)
  centralHi := (147645887035425096703/100000000000000000000)
  directionLo := (155632430062622975911/100000000000000000000)
  directionHi := (19454053757827871989/12500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree011.table
  base := (-163101176572159454964144556998816768007/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-36363382509823721916442096060000000000000)
      constant := (26081123273909694715485768260100574719405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree011.table
  base := (-433395504537820095691856680453633376509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-1005420828590322399331835604210000000000000)
      constant := (752086905528018112870060892783564560364738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155632430062622975911/100000000000000000000)
  centralHi := (19454053757827871989/12500000000000000000)
  directionLo := (163228669711901269961/100000000000000000000)
  directionHi := (81614334855950634981/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree012.table
  base := (-2742431045661099930066244167812018417407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-82742916884833707658053469340000000000000)
      constant := (65276582710358623270707714187195686904081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree012.table
  base := (-562761406677398402230609490526020937443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3382)
      previous := (2432)
      next := (0)
      square := (109462231098107026089349958190000000000000)
      linear := (-761856798018108392622771413580000000000000)
      constant := (635648837878288150894608236387593982856105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163228669711901269961/100000000000000000000)
  centralHi := (81614334855950634981/50000000000000000000)
  directionLo := (170486785249287512631/100000000000000000000)
  directionHi := (21310848156160939079/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree013.table
  base := (-1836415815635728795697861330248248402537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-46379534375009985741611373280000000000000)
      constant := (42796267251667385543302312130779777156871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree013.table
  base := (-930542166433456508611351664627693643783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-1280149565464002778536478636530000000000000)
      constant := (1251761859577606966748344310431777235007206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170486785249287512631/100000000000000000000)
  centralHi := (21310848156160939079/12500000000000000000)
  directionLo := (177448272105863012779/100000000000000000000)
  directionHi := (8872413605293150639/5000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree014.table
  base := (-2236497463234599375694076520459891133213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-51387610307603117654196011890000000000000)
      constant := (56123409030083401088385821432181850735379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree014.table
  base := (-901381062439125557535031713812516739083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-2835027867801685936277600305380000000000000)
      constant := (3271764003392319659399643229280274083804515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177448272105863012779/100000000000000000000)
  centralHi := (8872413605293150639/5000000000000000000)
  directionLo := (23018346827203717463/12500000000000000000)
  directionHi := (36829354923525947941/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree015.table
  base := (-2587715142359936666728813093381472076181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-56395686240196249566780650500000000000000)
      constant := (72343387185970183921584612537514974704923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree015.table
  base := (-649828108973209068539909236294541406259/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (-518292767445894385913707222950000000000000)
      constant := (699603056783181379671793163387740659369492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23018346827203717463/12500000000000000000)
  centralHi := (36829354923525947941/20000000000000000000)
  directionLo := (190610020541407653851/100000000000000000000)
  directionHi := (47652505135351913463/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree016.table
  base := (-725119322116029086847204825581809252571/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-61403762172789381479365289110000000000000)
      constant := (91279258316637347506923965140436970825172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree016.table
  base := (-581675327056804049495931527606194392347/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-1692242670774523347343443185010000000000000)
      constant := (2636085115506053493710549307983783869563635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190610020541407653851/100000000000000000000)
  centralHi := (47652505135351913463/25000000000000000000)
  directionLo := (24607647839237516117/12500000000000000000)
  directionHi := (196861182713900128937/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree017.table
  base := (-6362900757305973551941352291759047721003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-132823676210765026783899855440000000000000)
      constant := (225635384622570939506724004530096188742949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree017.table
  base := (-6373622624339247046837541404318370030317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-3659214078422727073891529402340000000000000)
      constant := (6489759233180775210138465402937868156084497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24607647839237516117/12500000000000000000)
  centralHi := (196861182713900128937/100000000000000000000)
  directionLo := (101459931239178471707/50000000000000000000)
  directionHi := (40583972495671388683/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree018.table
  base := (-6869810473026026806007137806044829689829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-142839828075951290609069132660000000000000)
      constant := (273772170337889276003805148337237895272907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree018.table
  base := (-6877063647342116365978753437206396014383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3382)
      previous := (2432)
      next := (0)
      square := (109462231098107026089349958190000000000000)
      linear := (-1311314271765469151032057478220000000000000)
      constant := (2615597016455878885271158535947421409799401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101459931239178471707/50000000000000000000)
  centralHi := (40583972495671388683/20000000000000000000)
  directionLo := (10440140793705204781/5000000000000000000)
  directionHi := (208802815874104095621/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree019.table
  base := (-1465431436801004188044936341730153859147/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-152855979941137554434238409880000000000000)
      constant := (326875824960647020289846690162936921972505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree019.table
  base := (-7332049972110311940684638516347326779591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-4208671552170087832300815466980000000000000)
      constant := (9340982782239739783315654832676577008167731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10440140793705204781/5000000000000000000)
  centralHi := (208802815874104095621/100000000000000000000)
  directionLo := (42904900067789338919/20000000000000000000)
  directionHi := (53631125084736673649/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree020.table
  base := (-3869224562289178644345099371781939021791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-81436065903161909129703843550000000000000)
      constant := (192443354253571174842606489679707036629553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree020.table
  base := (-7741741370748109792289125910111066818237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-4483400289043768211505458499300000000000000)
      constant := (10970884096401221898852729543259020330429217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42904900067789338919/20000000000000000000)
  centralHi := (53631125084736673649/25000000000000000000)
  directionLo := (55024373334910902729/25000000000000000000)
  directionHi := (220097493339643610917/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree021.table
  base := (-8105935471770423031734829224052800304523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-172888283671510082084576964320000000000000)
      constant := (447766584967960682124274630601102394823109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree021.table
  base := (-8108145778618662644096778823025631359543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3382)
      previous := (2432)
      next := (0)
      square := (109462231098107026089349958190000000000000)
      linear := (-1586043008639149530236700510540000000000000)
      constant := (4245191116506798634142635076237078401989921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55024373334910902729/25000000000000000000)
  centralHi := (220097493339643610917/100000000000000000000)
  directionLo := (112766408898122435123/50000000000000000000)
  directionHi := (225532817796244870247/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree022.table
  base := (-4215529287262669769596651312946925813447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-91452217768348172954873120770000000000000)
      constant := (257745467205525977159920621399902261171401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree022.table
  base := (-527033719669211048719904746762361412223/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-2516428881395564484957372281970000000000000)
      constant := (7317232355591480154977794284448608894317144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112766408898122435123/50000000000000000000)
  centralHi := (225532817796244870247/100000000000000000000)
  directionLo := (57710049618672304319/25000000000000000000)
  directionHi := (230840198474689217277/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree023.table
  base := (-8714743628998791611102429429733520949151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-192920587401882609734915518760000000000000)
      constant := (588044028501769524671287037784530143864433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree023.table
  base := (-4357867041033697606070403286109020245471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-2653793249832404674559693798130000000000000)
      constant := (8333592850743761239099767540635959707328811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57710049618672304319/25000000000000000000)
  centralHi := (230840198474689217277/100000000000000000000)
  directionLo := (11801413322199340843/5000000000000000000)
  directionHi := (236028266443986816861/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree024.table
  base := (-8957584273584323111399208827419739681901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-202936739267068873560084795980000000000000)
      constant := (665415775387423147491683029293864425407683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree024.table
  base := (-4479122801040698255583223055600107758141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (-930385872756414954720671771430000000000000)
      constant := (3138916570119905490649286124973183513004427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11801413322199340843/5000000000000000000)
  centralHi := (236028266443986816861/100000000000000000000)
  directionLo := (30138090488116465833/12500000000000000000)
  directionHi := (48220944780986345333/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree025.table
  base := (-1831992305505768228075377670927775764349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-212952891132255137385254073200000000000000)
      constant := (747599697740815402076044009221139060030335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree025.table
  base := (-572525152578669305897871991716645892531/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-2928521986706085053764336830450000000000000)
      constant := (10566627574325455027543723886416476282626168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30138090488116465833/12500000000000000000)
  centralHi := (48220944780986345333/20000000000000000000)
  directionLo := (24607647839237516117/10000000000000000000)
  directionHi := (246076478392375161171/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree026.table
  base := (-9322120030540986497136154331376172903233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-222969042997441401210423350420000000000000)
      constant := (834591636686899394839658310126605060645039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree026.table
  base := (-9322413593474340004598453878159894836747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-6131772710285850486733316693220000000000000)
      constant := (23566356957093325303702387463204608269933127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24607647839237516117/10000000000000000000)
  centralHi := (246076478392375161171/100000000000000000000)
  directionLo := (7842179782243213879/3125000000000000000)
  directionHi := (250949753031782844129/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree027.table
  base := (-9444216923694130612070085941098807636931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-232985194862627665035592627640000000000000)
      constant := (926388920827427811465843585891320270172173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree027.table
  base := (-2361103034477360638968563858328846770037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (-1067750241193255144322993287590000000000000)
      constant := (4355457293783754932334967768471372888368678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7842179782243213879/3125000000000000000)
  centralHi := (250949753031782844129/100000000000000000000)
  directionLo := (255730177873931268947/100000000000000000000)
  directionHi := (63932544468482817237/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree028.table
  base := (-9526353196582250274227169336609238152591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-243001346727813928860761904860000000000000)
      constant := (1022989833339303046540775571917642951405953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree028.table
  base := (-9526482863722476644391024993952505719757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-6681230184033211245142602757860000000000000)
      constant := (28832376647254789741854975392095799874631537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255730177873931268947/100000000000000000000)
  centralHi := (63932544468482817237/25000000000000000000)
  directionLo := (130211433065756796023/50000000000000000000)
  directionHi := (260422866131513592047/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree029.table
  base := (-1196074224346691240110440120430125268941/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-126508749296500096342965591040000000000000)
      constant := (562196635073932982315380144315751481712012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree029.table
  base := (-9568679834176036669881043398552857149589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-6955958920906891624347245790180000000000000)
      constant := (31665230795712574917760776902144238568338649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130211433065756796023/50000000000000000000)
  centralHi := (260422866131513592047/100000000000000000000)
  directionLo := (132516239130221293341/50000000000000000000)
  directionHi := (265032478260442586683/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree030.table
  base := (-9570980520585883097870091276249282085577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-263033650458186456511100459300000000000000)
      constant := (1230598520613712035456671578303762204545191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree030.table
  base := (-9571037556735000080273396860898331043989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3382)
      previous := (2432)
      next := (0)
      square := (109462231098107026089349958190000000000000)
      linear := (-2410229219260190667850629607500000000000000)
      constant := (11543763456383168791042586856282555350269683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132516239130221293341/50000000000000000000)
  centralHi := (265032478260442586683/100000000000000000000)
  directionLo := (67390819043468235391/25000000000000000000)
  directionHi := (53912655234774588313/20000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree031.table
  base := (-1191692539002685373533492195557326595411/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-136524901161686360168134868260000000000000)
      constant := (670802563395402157453065733507101791512052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree031.table
  base := (-381343123538466257847525881357070229391/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-7505416394654252382756531854820000000000000)
      constant := (37730545243373993195041318093507619117738275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67390819043468235391/25000000000000000000)
  centralHi := (53912655234774588313/20000000000000000000)
  directionLo := (17126198086547229331/6250000000000000000)
  directionHi := (274019169384755669297/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree032.table
  base := (-2364072639228211904862927117363426174983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-141532977094279492080719506870000000000000)
      constant := (728706396542994998256885463929643510050578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree032.table
  base := (-118203944460899984271545097286083720819/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-3890072565763966380980587443570000000000000)
      constant := (20481494466928097304195161705987502885763160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17126198086547229331/6250000000000000000)
  centralHi := (274019169384755669297/100000000000000000000)
  directionLo := (139201877249402730413/50000000000000000000)
  directionHi := (278403754498805460827/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree033.table
  base := (-4669621252403099509887362270351497059079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-146541053026872623993304145480000000000000)
      constant := (789010664128491652898791755749024549995657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree033.table
  base := (-933925903704060569084909989717201880607/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (-1342478978066935523527636319910000000000000)
      constant := (7388102879189479829812143046986340561335645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139201877249402730413/50000000000000000000)
  centralHi := (278403754498805460827/100000000000000000000)
  directionLo := (282720349192892135993/100000000000000000000)
  directionHi := (141360174596446067997/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree034.table
  base := (-45912017290222643868156562716704802191/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-151549128959465755905888784090000000000000)
      constant := (851715304081976692911432831461601836275300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree034.table
  base := (-918241438305421270568646797045401810311/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-4164801302637646760185230475890000000000000)
      constant := (23913713790095117376162498017420802845336255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282720349192892135993/100000000000000000000)
  centralHi := (141360174596446067997/50000000000000000000)
  directionLo := (286972021591775716847/100000000000000000000)
  directionHi := (17935751349485982303/6250000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree035.table
  base := (-561611136200799833245322486029935043597/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-156557204892058887818473422700000000000000)
      constant := (916820275921477954462127349024928834070808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree035.table
  base := (-8985785394139699943060270698570544296747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-8604331342148973899575103984100000000000000)
      constant := (51459418105171123936764264229356120167793127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286972021591775716847/100000000000000000000)
  centralHi := (17935751349485982303/6250000000000000000)
  directionLo := (291161615782696039459/100000000000000000000)
  directionHi := (14558080789134801973/5000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree036.table
  base := (-4374684897725338948185052282828387306183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-161565280824652019731058061310000000000000)
      constant := (984325553066308215336307682671917415794889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree036.table
  base := (-2187343639341588486465123620467650538701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (-1479843346503775713129957836070000000000000)
      constant := (9204097951419124001500693184616898935157494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291161615782696039459/100000000000000000000)
  centralHi := (14558080789134801973/5000000000000000000)
  directionLo := (73822943517712548351/25000000000000000000)
  directionHi := (59058354814170038681/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree037.table
  base := (-8473180379659224533220008467677229120337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-333146713514490303287285399840000000000000)
      constant := (2108462235793617031941632018339487104954271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree037.table
  base := (-4236591760406501628925624841021803425951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-4576894407948167328992195024370000000000000)
      constant := (29561467816876456333728477006930992227488491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73822943517712548351/25000000000000000000)
  centralHi := (59058354814170038681/20000000000000000000)
  directionLo := (37420619558821977973/12500000000000000000)
  directionHi := (59872991294115164757/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree038.table
  base := (-8157211324166501529918927831451375600541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-343162865379676567112454677060000000000000)
      constant := (2253073917156380619844755699105326614790803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree038.table
  base := (-4078606697561385654980436854067920021451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-4714258776385007518594516540530000000000000)
      constant := (31577230685550218128663271038542824710153991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37420619558821977973/12500000000000000000)
  centralHi := (59872991294115164757/20000000000000000000)
  directionLo := (60676691568130008243/20000000000000000000)
  directionHi := (2370183264380078447/781250000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree039.table
  base := (-1560292716210679258910279723602262855919/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-353179017244862830937623954280000000000000)
      constant := (2402486134035532108444549296303807657246885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree039.table
  base := (-7801464945768452268440153801305448015843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3382)
      previous := (2432)
      next := (0)
      square := (109462231098107026089349958190000000000000)
      linear := (-3234415429881231805464558704460000000000000)
      constant := (22439721523068434085434603984560266453576021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60676691568130008243/20000000000000000000)
  centralHi := (2370183264380078447/781250000000000000)
  directionLo := (76837355750665478373/25000000000000000000)
  directionHi := (307349423002661913493/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree040.table
  base := (-7405937816792456413738825745393829997101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-363195169110049094762793231500000000000000)
      constant := (2556698875101038188768448926328304890049283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree040.table
  base := (-1481187743140481424930089933480495997621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-9977975026517375795598319145700000000000000)
      constant := (71617044978852376969353899538662261685459805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76837355750665478373/25000000000000000000)
  centralHi := (307349423002661913493/100000000000000000000)
  directionLo := (311264860125245951823/100000000000000000000)
  directionHi := (19454053757827871989/6250000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree041.table
  base := (-6970634511809414812161280224167312291921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-373211320975235358587962508720000000000000)
      constant := (2715712132185661401096893381999155691037343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree041.table
  base := (-6970635103652026844938533341777146773723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-10252703763391056174802962178020000000000000)
      constant := (76048102417025787942923636467804289630861143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311264860125245951823/100000000000000000000)
  centralHi := (19454053757827871989/6250000000000000000)
  directionLo := (157565826305633807093/50000000000000000000)
  directionHi := (315131652611267614187/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree042.table
  base := (-6495554024633554358160405725085422210203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-383227472840421622413131785940000000000000)
      constant := (2879525899194403936668074720913547822426549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree042.table
  base := (-1299110882829635899757569005584399675411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3382)
      previous := (2432)
      next := (0)
      square := (109462231098107026089349958190000000000000)
      linear := (-3509144166754912184669201736780000000000000)
      constant := (26870778914648622244373374562567934248310585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157565826305633807093/50000000000000000000)
  centralHi := (315131652611267614187/100000000000000000000)
  directionLo := (159475784843834812919/50000000000000000000)
  directionHi := (318951569687669625839/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree043.table
  base := (-5980696633274683730330772819798711464851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-393243624705607886238301063160000000000000)
      constant := (3048140171401099047945885243353421905097533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree043.table
  base := (-5980696889533920919697413731869169106313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-10802161237138416933212248242660000000000000)
      constant := (85309747848377150712367306884592051380202333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159475784843834812919/50000000000000000000)
  centralHi := (318951569687669625839/100000000000000000000)
  directionLo := (322726275866945945343/100000000000000000000)
  directionHi := (1260649515105257599/390625000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree044.table
  base := (-271303128097481766500681534476946581327/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-201629888285397075031735170190000000000000)
      constant := (1610777472497030292053761856618919081174410) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree044.table
  base := (-2713031365241015374798291678360850828739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-5538444987006048656208445637490000000000000)
      constant := (45070167819105417012509808603472369469608799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322726275866945945343/100000000000000000000)
  centralHi := (1260649515105257599/390625000000000000)
  directionLo := (326457339423802539923/100000000000000000000)
  directionHi := (81614334855950634981/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree045.table
  base := (-4831651998380363603360057608288984603357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-413275928435980413888639617600000000000000)
      constant := (3399770216782015319568421799909087261742931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree045.table
  base := (-1207913027295391767764441476522119986127/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (-1891936451814296281936922384550000000000000)
      constant := (15850683339068689835196052924184231284245138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326457339423802539923/100000000000000000000)
  centralHi := (81614334855950634981/25000000000000000000)
  directionLo := (2641169920075723331/800000000000000000)
  directionHi := (41268280001183177047/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree046.table
  base := (-4197465105021540413659751016849937208527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-423292080301166677713808894820000000000000)
      constant := (3582785984003233832652654646873551067455041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree046.table
  base := (-524683147230622697837156051642125044281/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-5813173723879729035413088669810000000000000)
      constant := (50100520483557775170586266075425058418700084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2641169920075723331/800000000000000000)
  centralHi := (41268280001183177047/12500000000000000000)
  directionLo := (16689718775424832367/5000000000000000000)
  directionHi := (333794375508496647341/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree047.table
  base := (-3523502026377316125706762901804420481103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-433308232166352941538978172040000000000000)
      constant := (3770602244201145567158723370359324851821249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree047.table
  base := (-352350207422614708962707344742207671521/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-5950538092316569225015410185970000000000000)
      constant := (52715579186546020198730916742376633393859305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16689718775424832367/5000000000000000000)
  centralHi := (333794375508496647341/100000000000000000000)
  directionLo := (337403068228234980909/100000000000000000000)
  directionHi := (33740306822823498091/10000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree048.table
  base := (-351220361724573626946276193432792713633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-221662192015769602682073724630000000000000)
      constant := (1981609497571409626196726496766570095472956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree048.table
  base := (-2809762925227146099325301486772688086733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3382)
      previous := (2432)
      next := (0)
      square := (109462231098107026089349958190000000000000)
      linear := (-4058601640502272943078487801420000000000000)
      constant := (36931484064697851103037263929163778722729851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (337403068228234980909/100000000000000000000)
  centralHi := (33740306822823498091/10000000000000000000)
  directionLo := (340973570498575025263/100000000000000000000)
  directionHi := (21310848156160939079/6250000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree049.table
  base := (-514061957160199617696766920346110884051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-226670267948362734594658363240000000000000)
      constant := (2080318117382555209384357456013232229942266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree049.table
  base := (-2056247849281293227470404488577519317087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-12450533658380499208440106436580000000000000)
      constant := (116290922375759197667525988430622918633457067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340973570498575025263/100000000000000000000)
  centralHi := (21310848156160939079/6250000000000000000)
  directionLo := (172253534874662612819/50000000000000000000)
  directionHi := (344507069749325225639/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree050.table
  base := (-1262956944399697614529567312722136249051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-463356687761911733014486003700000000000000)
      constant := (4362853961138693263190581215683723683766133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree050.table
  base := (-252591391590203409758441420349975924861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-12725262395254179587644749468900000000000000)
      constant := (121920568866881818756903433900296805252444005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172253534874662612819/50000000000000000000)
  centralHi := (344507069749325225639/100000000000000000000)
  directionLo := (348004693123506826033/100000000000000000000)
  directionHi := (174002346561753413017/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree051.table
  base := (-53736293515705917495149317709203919491/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-236686419813548998419827640460000000000000)
      constant := (2284936086221838825237636320400774133474612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree051.table
  base := (-85978071404114289458893430151748715939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3382)
      previous := (2432)
      next := (0)
      square := (109462231098107026089349958190000000000000)
      linear := (-4333330377375953322283130833740000000000000)
      constant := (42561130539635481348162134451693912232306665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (348004693123506826033/100000000000000000000)
  centralHi := (174002346561753413017/50000000000000000000)
  directionLo := (87866877919350916511/25000000000000000000)
  directionHi := (70293502335480733209/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree052.table
  base := (22147592928743092363757571779659994277/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-241694495746142130332412279070000000000000)
      constant := (2390845433476376621013429950522542199027090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree052.table
  base := (55368981592202957346798517672370312663/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-6637359934500770173027017766770000000000000)
      constant := (66789695292789266393899434349806471894049268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87866877919350916511/25000000000000000000)
  centralHi := (70293502335480733209/20000000000000000000)
  directionLo := (354896544211726025559/100000000000000000000)
  directionHi := (8872413605293150639/2500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree053.table
  base := (169446197354823701158353660594332386597/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-246702571678735262244996917680000000000000)
      constant := (2499155021509622476050414046865414602288596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree053.table
  base := (338892393752184322083372967192510219857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-6774724302937610362629339282930000000000000)
      constant := (69804282861344788783262356012042724381828726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (354896544211726025559/100000000000000000000)
  centralHi := (8872413605293150639/2500000000000000000)
  directionLo := (358292760772730836261/100000000000000000000)
  directionHi := (179146380386365418131/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree054.table
  base := (1153981360016279835880113629256957512781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-251710647611328394157581556290000000000000)
      constant := (2609864849534196092017432909577368277717277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree054.table
  base := (576990679380066103541820841958687423617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (-2304029557124816850743886933030000000000000)
      constant := (24295152831314416428861998497319358351626802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (358292760772730836261/100000000000000000000)
  centralHi := (179146380386365418131/50000000000000000000)
  directionLo := (90414271464349397499/25000000000000000000)
  directionHi := (361657085857397589997/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree055.table
  base := (3300131193366592882801964091737944437327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-513437447087843052140332389800000000000000)
      constant := (5445949833590761892245765595809545055434559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree055.table
  base := (825032797929723697184081269940576680513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-7049453039811290741833982315250000000000000)
      constant := (76033222170261663202060051869805449392710934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90414271464349397499/25000000000000000000)
  centralHi := (361657085857397589997/100000000000000000000)
  directionLo := (364990401352672252827/100000000000000000000)
  directionHi := (91247600338168063207/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree056.table
  base := (2166037456794940709058073624353002629519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-261726799476514657982750833510000000000000)
      constant := (2838485222568545171860418625294001044701823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree056.table
  base := (4332074912509425912408221233003460707871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-14373634816496261862872607662820000000000000)
      constant := (158495147741541363112037780632028588464912789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (364990401352672252827/100000000000000000000)
  centralHi := (91247600338168063207/25000000000000000000)
  directionLo := (23018346827203717463/6250000000000000000)
  directionHi := (368293549235259479409/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree057.table
  base := (5403793798744708530344810380037532783359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-533469750818215579790670944240000000000000)
      constant := (5912791532314096353754995355550638057317103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree057.table
  base := (2701896899018167663099858210774073730351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (-2441393925561657040346208449190000000000000)
      constant := (27509504525561487314708617904968433280743703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23018346827203717463/6250000000000000000)
  centralHi := (368293549235259479409/100000000000000000000)
  directionLo := (92891833513845628263/25000000000000000000)
  directionHi := (371567334055382513053/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree058.table
  base := (3257643884979908158777334666351246634753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-271742951341700921807920110730000000000000)
      constant := (3076706546890484269007687040047971192790801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree058.table
  base := (3257643884747732435014702849488403018207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-7461546145121811310640946863730000000000000)
      constant := (85876041269917450068642259631275176985357013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92891833513845628263/25000000000000000000)
  centralHi := (371567334055382513053/100000000000000000000)
  directionLo := (374812525225270379619/100000000000000000000)
  directionHi := (18740626261263518981/5000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree059.table
  base := (12266490802035175404482581032798785119/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-553502054548588107441009498680000000000000)
      constant := (6398835128246332153918923537883487091889375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree059.table
  base := (3833278375483820524968431136405855110097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-7598910513558651500243268379890000000000000)
      constant := (89290156933046195612704190116250287495534523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374812525225270379619/100000000000000000000)
  centralHi := (18740626261263518981/5000000000000000000)
  directionLo := (378029859130814781489/100000000000000000000)
  directionHi := (37802985913081478149/10000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree060.table
  base := (1107200083683537001872484585863532347851/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-281759103206887185633089387950000000000000)
      constant := (3324528817232783802440922860838720199653868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree060.table
  base := (2214400167317213444008432227773026966517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (-2578758293998497229948529965350000000000000)
      constant := (30923620183091656086894089061698546251754202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (378029859130814781489/100000000000000000000)
  centralHi := (37802985913081478149/10000000000000000000)
  directionLo := (381220041082815307703/100000000000000000000)
  directionHi := (47652505135351913463/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree061.table
  base := (5044209726972044822278472357793942356849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-286767179139480317545674026560000000000000)
      constant := (3452040305619197828358543936187497020066433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree061.table
  base := (2017683890762681960392674998961513058203/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-15747278500864663758895822824420000000000000)
      constant := (192636304204808702825075288221496672468575885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (381220041082815307703/100000000000000000000)
  centralHi := (47652505135351913463/12500000000000000000)
  directionLo := (192191873561229894543/50000000000000000000)
  directionHi := (384383747122459789087/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree062.table
  base := (11359013036573243673731783494296122181643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-583550510144146898916517330340000000000000)
      constant := (7163904057406672238097032416443034077087931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree062.table
  base := (177484578695119224878352923843568885993/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-8011003618869172069050232928370000000000000)
      constant := (99932031576802255798470497418374339797465184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192191873561229894543/50000000000000000000)
  centralHi := (384383747122459789087/100000000000000000000)
  directionLo := (387521625694131858949/100000000000000000000)
  directionHi := (7750432513882637179/2000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree063.table
  base := (6334690675794243965606002364152386486389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-296783331004666581370843303780000000000000)
      constant := (3714263985926176878054854376435590570268613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree063.table
  base := (12669381351532406742740509451220192034769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3382)
      previous := (2432)
      next := (0)
      square := (109462231098107026089349958190000000000000)
      linear := (-5432245324870674839101702963020000000000000)
      constant := (69074999304917977298634715793076689381319657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387521625694131858949/100000000000000000000)
  centralHi := (7750432513882637179/2000000000000000000)
  directionLo := (39063429919727038807/10000000000000000000)
  directionHi := (390634299197270388071/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree064.table
  base := (7009762167735070406488924849439130852127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-301791406937259713283427942390000000000000)
      constant := (3848976176747802811743390491720465224486159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree064.table
  base := (219055067741147019961643635337081980123/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-8285732355742852448254875960690000000000000)
      constant := (107359554229551943223291302558071060124046624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39063429919727038807/10000000000000000000)
  centralHi := (390634299197270388071/100000000000000000000)
  directionLo := (24607647839237516117/6250000000000000000)
  directionHi := (393722365427800257873/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree065.table
  base := (15409441926842117619543445534239884301409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-613598965739705690392025162000000000000000)
      constant := (7972177201293034400336989269332078033123953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree065.table
  base := (7704720963409031211658905023319256497277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-8423096724179692637857197476850000000000000)
      constant := (111173197379242181530413349293703538732250143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24607647839237516117/6250000000000000000)
  centralHi := (393722365427800257873/100000000000000000000)
  directionLo := (396786398918589454869/100000000000000000000)
  directionHi := (39678639891858945487/10000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree066.table
  base := (3367826813274871343818481943946040835953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-623615117604891954217194439220000000000000)
      constant := (8251202514236029038919455107795413471056005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree066.table
  base := (8419567033179302487057502756983703467497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (-2853487030872177609153172997670000000000000)
      constant := (38351142797610653224184737891098506630527041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396786398918589454869/100000000000000000000)
  centralHi := (39678639891858945487/10000000000000000000)
  directionLo := (99956738046861343801/25000000000000000000)
  directionHi := (79965390437489075041/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree067.table
  base := (18308600696691009432964255408131960371437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-633631269470078218042363716440000000000000)
      constant := (8535028291349200111696950222428243326314429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree067.table
  base := (2288575087085087008877597091380087047843/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-8697825461053373017061840509170000000000000)
      constant := (119000247257153866422592673161533839819839748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99956738046861343801/25000000000000000000)
  centralHi := (79965390437489075041/20000000000000000000)
  directionLo := (201422278450163906693/50000000000000000000)
  directionHi := (402844556900327813387/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree068.table
  base := (9908920881141937255420642959626172999071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-321823710667632240933766496830000000000000)
      constant := (4411827265844454098707036884833644940984207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree068.table
  base := (19817841762277122619873549294562843110591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-17670379658980426413328324050660000000000000)
      constant := (246027307918937992750837292865724344987761269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201422278450163906693/50000000000000000000)
  centralHi := (402844556900327813387/100000000000000000000)
  directionLo := (101459931239178471707/25000000000000000000)
  directionHi := (405839724956713886829/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree069.table
  base := (854674288377226044350895150871367300291/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-653663573200450745692702270880000000000000)
      constant := (9117081234341874181723656667330331102623675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree069.table
  base := (21366857209426231276394119512369493698519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3382)
      previous := (2432)
      next := (0)
      square := (109462231098107026089349958190000000000000)
      linear := (-5981702798618035597510989027660000000000000)
      constant := (84729098991632153392346704159952532535873407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101459931239178471707/25000000000000000000)
  centralHi := (405839724956713886829/100000000000000000000)
  directionLo := (408812949503389507851/100000000000000000000)
  directionHi := (102203237375847376963/25000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree070.table
  base := (22955646986117649878724101761511869518533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-663679725065637009517871548100000000000000)
      constant := (9415308398423865345709130567945701781815061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree070.table
  base := (5738911746528689228835507325182874268799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-9109918566363893585868805057650000000000000)
      constant := (131240230829154523215654217452517878578757482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408812949503389507851/100000000000000000000)
  centralHi := (102203237375847376963/25000000000000000000)
  directionLo := (51470588235294117647/12500000000000000000)
  directionHi := (411764705882352941177/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree071.table
  base := (2458421104196664952144520552804064594729/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-336847938465411636671520412660000000000000)
      constant := (4859168011539225963641612116193345490551965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree071.table
  base := (24584211041964756139292421237417131222619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-18494565869601467550942253147620000000000000)
      constant := (270906801946052275494224250584454463231182121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51470588235294117647/12500000000000000000)
  centralHi := (411764705882352941177/100000000000000000000)
  directionLo := (103673863129497453999/25000000000000000000)
  directionHi := (414695452517989815997/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree072.table
  base := (1050101973126624880394151292235131449873/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-683712028796009537168210102540000000000000)
      constant := (10026164107475829449985545228639930866196025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree072.table
  base := (328156866602054786842962698604259395607/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (-3128215767745857988357816029990000000000000)
      constant := (46577719635953585008569426542978067501114840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103673863129497453999/25000000000000000000)
  centralHi := (414695452517989815997/100000000000000000000)
  directionLo := (10440140793705204781/2500000000000000000)
  directionHi := (417605631748208191241/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree073.table
  base := (436885340584423087142600312213267986353/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-346864090330597900496689689880000000000000)
      constant := (5169396325405851293890047775389017784576032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree073.table
  base := (27960661797402266786112481068814888912341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-19044023343348828309351539212260000000000000)
      constant := (288159009245600831018753891452506034010764519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10440140793705204781/2500000000000000000)
  centralHi := (417605631748208191241/100000000000000000000)
  directionLo := (42049567060380038161/10000000000000000000)
  directionHi := (420495670603800381611/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree074.table
  base := (14854274201902901510121587760074273744381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-351872166263191032409274328490000000000000)
      constant := (5328110826153113358107768083601262653654477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree074.table
  base := (14854274201902636259317380168686825916647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-9659376040111254344278091122290000000000000)
      constant := (148492438107317234684249132630867253095740973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42049567060380038161/10000000000000000000)
  centralHi := (420495670603800381611/100000000000000000000)
  directionLo := (423365981539919566989/100000000000000000000)
  directionHi := (42336598153991956699/10000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree075.table
  base := (15748104551439892772433738278113657565753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-356880242195784164321858967100000000000000)
      constant := (5489225555601501808894072673852932178617801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree075.table
  base := (7874052275719859616605118503727946097371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (-3265580136182698177960137546150000000000000)
      constant := (50990653117066616115029984902140751505795526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423365981539919566989/100000000000000000000)
  centralHi := (42336598153991956699/10000000000000000000)
  directionLo := (426216963123218781579/100000000000000000000)
  directionHi := (21310848156160939079/5000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree076.table
  base := (266589150811633042781236503851616190777/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-723776636256754592468887211420000000000000)
      constant := (11305481026768128080841062170444684405401125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree076.table
  base := (33323643851453903291745628628492690673873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-19868209553969869446965468309220000000000000)
      constant := (315036136689081087629783510901758145019307707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426216963123218781579/100000000000000000000)
  centralHi := (21310848156160939079/5000000000000000000)
  directionLo := (429049000677893389191/100000000000000000000)
  directionHi := (53631125084736673649/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree077.table
  base := (3519085260762779410529496456035722552587/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-366896394060970428147028244320000000000000)
      constant := (5818655699144641184439012820708036416969895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree077.table
  base := (7038170521525529115810642527950534373399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-20142938290843549826170111341540000000000000)
      constant := (324261530155446073357568401432366476386950705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429049000677893389191/100000000000000000000)
  centralHi := (53631125084736673649/12500000000000000000)
  directionLo := (431862466893591813467/100000000000000000000)
  directionHi := (107965616723397953367/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree078.table
  base := (18548917665359484493051861586816010371659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-371904469993563560059612882930000000000000)
      constant := (5986971112537437874380195736295872176318203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree078.table
  base := (9274458832679717959197546661456486611147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (-3402944504619538367562459062310000000000000)
      constant := (55603349847136951776818622653125684903010982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (431862466893591813467/100000000000000000000)
  centralHi := (107965616723397953367/25000000000000000000)
  directionLo := (54332215299738723517/12500000000000000000)
  directionHi := (434657722397909788137/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree079.table
  base := (9761147995304240759196093319523106342121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-376912545926156691972197521540000000000000)
      constant := (6157686753226613228641059874868785615632114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree079.table
  base := (39044591981216899497352456175751635427621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-20692395764590910584579397406180000000000000)
      constant := (343111843453072596241283234998750000661278039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54332215299738723517/12500000000000000000)
  centralHi := (434657722397909788137/100000000000000000000)
  directionLo := (218717558147978903573/50000000000000000000)
  directionHi := (437435116295957807147/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree080.table
  base := (41031122520736433041991224272097896532227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-763841243717499647769564320300000000000000)
      constant := (12661605241771783659782333732625664241047859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree080.table
  base := (41031122520736391487802999306185851561111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-20967124501464590963784040438500000000000000)
      constant := (352736763248579860382204805609539305866549949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218717558147978903573/50000000000000000000)
  centralHi := (437435116295957807147/100000000000000000000)
  directionLo := (440194986679287221833/100000000000000000000)
  directionHi := (220097493339643610917/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree081.table
  base := (8611485382394767072207596597246216038507/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-773857395582685911594733597520000000000000)
      constant := (13012637430396387114369366437375928363273095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree081.table
  base := (21528713455986904093475826590515199012941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (-3540308873056378557164780578470000000000000)
      constant := (60415809742036863066258360500028825448979973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440194986679287221833/100000000000000000000)
  centralHi := (220097493339643610917/50000000000000000000)
  directionLo := (221468830553137645053/50000000000000000000)
  directionHi := (442937661106275290107/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree082.table
  base := (2820219069916623057883000158328105691333/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-391936773723936087709951437370000000000000)
      constant := (6684235035855281201445337433452622374021288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree082.table
  base := (11280876279666487789266343048059244934871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-10758290987605975861096663251570000000000000)
      constant := (186193064523675871102199919618278386850211578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221468830553137645053/50000000000000000000)
  centralHi := (442937661106275290107/100000000000000000000)
  directionLo := (445663457055901433303/100000000000000000000)
  directionHi := (55707932131987679163/12500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree083.table
  base := (9445871421110098524750842980891955788877/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-793889699313058439245072151960000000000000)
      constant := (13729103165114849726416638865065816242054545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree083.table
  base := (47229357105550481005410776838841920134291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-21791310712085632101397969535460000000000000)
      constant := (382410575017786138021489213127748441341639569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (445663457055901433303/100000000000000000000)
  centralHi := (55707932131987679163/12500000000000000000)
  directionLo := (224186341178347116659/50000000000000000000)
  directionHi := (448372682356694233319/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree084.table
  base := (49374982838328306741027032142429913419423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-803905851178244703070241429180000000000000)
      constant := (14094536710026164389828135436581308528130191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree084.table
  base := (49374982838328299144856705098152706530401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3382)
      previous := (2432)
      next := (0)
      square := (109462231098107026089349958190000000000000)
      linear := (-7355346482986437493534204189260000000000000)
      constant := (130856065449260359865775027101777364099151353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224186341178347116659/50000000000000000000)
  centralHi := (448372682356694233319/100000000000000000000)
  directionLo := (451065635592489740493/100000000000000000000)
  directionHi := (225532817796244870247/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree085.table
  base := (10312076456725539018941998790928876000221/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-813922003043430966895410706400000000000000)
      constant := (14464770705877187218010144756478954460018785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree085.table
  base := (51560382283627690128596929586755510242623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-22340768185832992859807255600100000000000000)
      constant := (402858993022018949541823385400320779201363957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451065635592489740493/100000000000000000000)
  centralHi := (225532817796244870247/50000000000000000000)
  directionLo := (56717825810814384151/12500000000000000000)
  directionHi := (453742606486515073209/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree086.table
  base := (10757111081794026183432519671680243839301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-823938154908617230720579983620000000000000)
      constant := (14839805152115783255912778291052820726340585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree086.table
  base := (13446388852242531917674753549500615537801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-11307748461353336619505949316210000000000000)
      constant := (206641482512796052144870568619881565063701318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56717825810814384151/12500000000000000000)
  centralHi := (453742606486515073209/100000000000000000000)
  directionLo := (45640387626519583907/10000000000000000000)
  directionHi := (456403876265195839071/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree087.table
  base := (56050502182737655588462935416930454224783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-833954306773803494545749260840000000000000)
      constant := (15219640048204447206997363571377817721821311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree087.table
  base := (56050502182737653466308130516093020677331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3382)
      previous := (2432)
      next := (0)
      square := (109462231098107026089349958190000000000000)
      linear := (-7630075219860117872738847221580000000000000)
      constant := (141280037447995966993049990193602232163631643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45640387626519583907/10000000000000000000)
  centralHi := (456403876265195839071/100000000000000000000)
  directionLo := (45904971800298049737/10000000000000000000)
  directionHi := (459049718002980497371/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree088.table
  base := (29177611287070872455722147270602881112961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-421985229319494879185459269030000000000000)
      constant := (7802137696809887079956033258720248978920337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree088.table
  base := (3647201410883858970269732208595153648279/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-11582477198227016998710592348530000000000000)
      constant := (217265217481537203549065527456521404196480488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45904971800298049737/10000000000000000000)
  centralHi := (459049718002980497371/100000000000000000000)
  directionLo := (461680396949378434553/100000000000000000000)
  directionHi := (230840198474689217277/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree089.table
  base := (30349858276596791428199044649293797125737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-426993305252088011098043907640000000000000)
      constant := (7996855593925977121075920579942994551137529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree089.table
  base := (7587464569149197743721027088958992619693/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-11719841566663857188312913864690000000000000)
      constant := (222676966434543378075450354945568710449756348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461680396949378434553/100000000000000000000)
  centralHi := (230840198474689217277/50000000000000000000)
  directionLo := (464296170839320365939/100000000000000000000)
  directionHi := (23214808541966018297/5000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree090.table
  base := (63083984090675667582157943339713382594339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-864002762369362286021257092500000000000000)
      constant := (16387947430404289922416859100775127504103763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree090.table
  base := (7885498011334458373702278495629384746909/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1691)
      previous := (1216)
      next := (0)
      square := (54731115549053513044674979095000000000000)
      linear := (-3952401978366899125971745126950000000000000)
      constant := (76051767674769019138801695975325183465108308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464296170839320365939/100000000000000000000)
  centralHi := (23214808541966018297/5000000000000000000)
  directionLo := (93379458037573785547/20000000000000000000)
  directionHi := (58362161273483615967/12500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree091.table
  base := (65508025158114679095209834997059607665899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-874018914234548549846426369720000000000000)
      constant := (16786984120792734760817381971760013330320283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree091.table
  base := (65508025158114678707970464833215328324557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-23989140607075075135035113794020000000000000)
      constant := (467400454488587229293283517318125835700971663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93379458037573785547/20000000000000000000)
  centralHi := (58362161273483615967/12500000000000000000)
  directionLo := (234741999285116642763/50000000000000000000)
  directionHi := (469483998570233285527/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree092.table
  base := (67971839727755542161388664645786726591269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-884035066099734813671595646940000000000000)
      constant := (17190821258545452478372603079218374352051573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree092.table
  base := (67971839727755541908332693179548842677223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-24263869343948755514239756826340000000000000)
      constant := (478623478176266520017130798820932918788845357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234741999285116642763/50000000000000000000)
  centralHi := (469483998570233285527/100000000000000000000)
  directionLo := (11801413322199340843/2500000000000000000)
  directionHi := (472056532887973633721/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree093.table
  base := (70475427772536622056886107590006598101589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-894051217964921077496764924160000000000000)
      constant := (17599458843202395284777780903320112167727013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree093.table
  base := (70475427772536621891526610458828474734899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3382)
      previous := (2432)
      next := (0)
      square := (109462231098107026089349958190000000000000)
      linear := (-8179532693607478631148133286220000000000000)
      constant := (163326559033076898892476393164040756634439547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11801413322199340843/2500000000000000000)
  centralHi := (472056532887973633721/100000000000000000000)
  directionLo := (118653780905554758489/25000000000000000000)
  directionHi := (474615123622219033957/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree094.table
  base := (36509394633032997228188418809303321429927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-452033684915053670660967100690000000000000)
      constant := (9006448437157450233251192449238156464308759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree094.table
  base := (36509394633032997174164314784133402239277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (5073)
      previous := (3648)
      next := (0)
      square := (164193346647160539134024937285000000000000)
      linear := (-12406663408848058136324521445490000000000000)
      constant := (250734525622682933008122516425757231627828143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118653780905554758489/25000000000000000000)
  centralHi := (474615123622219033957/100000000000000000000)
  directionLo := (47715999507466463553/10000000000000000000)
  directionHi := (477159995074664635531/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree095.table
  base := (75601924182598734224302576848916478270269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-914083521695293605147103478600000000000000)
      constant := (18431135351445304296241924340681580130594573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree095.table
  base := (15120384836519746830741245147857878538291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-25088055554569796651853685923300000000000000)
      constant := (513091600602855107401188430030333831245377845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47715999507466463553/10000000000000000000)
  centralHi := (477159995074664635531/100000000000000000000)
  directionLo := (479691365597061484591/100000000000000000000)
  directionHi := (29980710349816342787/6250000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree096.table
  base := (39112416248507585558831982746986425812581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-462049836780239934486136377910000000000000)
      constant := (9427087137083286189932705056778769238813877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree096.table
  base := (78224832497015171071540325780672086177151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3382)
      previous := (2432)
      next := (0)
      square := (109462231098107026089349958190000000000000)
      linear := (-8454261430481159010352776318540000000000000)
      constant := (174949108386722830731293572144602829185104103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479691365597061484591/100000000000000000000)
  centralHi := (29980710349816342787/6250000000000000000)
  directionLo := (30138090488116465833/6250000000000000000)
  directionHi := (482209447809863453329/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree097.table
  base := (40443757092400031720371637043589034829969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85000000000000000000000000000000000000000
      center := (190)
      previous := (133)
      next := (0)
      square := (6081235061005945893852775455000000000000)
      linear := (-467057912712833066398721016520000000000000)
      constant := (9641006821030972804272820408086013592109473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree097.table
  base := (80887514184800063410610308598951368170147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-25637513028317157410262971987940000000000000)
      constant := (536736224906053524458051626980038677990097473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell021.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30138090488116465833/6250000000000000000)
  centralHi := (482209447809863453329/100000000000000000000)
  directionLo := (484714448810650938273/100000000000000000000)
  directionHi := (242357224405325469137/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree098.table
  base := (83589969222022643528617604167322005416483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (380)
      previous := (266)
      next := (0)
      square := (12162470122011891787705550910000000000000)
      linear := (-944131977290852396622611310260000000000000)
      constant := (19714653454724600931978927174684474092080211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree098.table
  base := (83589969222022643508932509621036110290417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (10146)
      previous := (7296)
      next := (0)
      square := (328386693294321078268049874570000000000000)
      linear := (-25912241765190837789467615020260000000000000)
      constant := (548758299829525981836850659629975574623301403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell021.Kernel098
