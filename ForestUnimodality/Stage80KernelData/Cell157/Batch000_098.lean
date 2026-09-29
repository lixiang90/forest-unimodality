import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell157.Parameters
import ForestUnimodality.BinomialMassData.Q95599_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95599_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch000_049
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree000.table
  base := (77775379769657858244329419/2000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1197706686216491456242749800000000000000)
      linear := (-74505534505800441458234218000000000000)
      constant := (388876898848289291221647095000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree000.table
  base := (77775379769657858244329419/2000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1197706686216491456242749800000000000000)
      linear := (-74505534505800441458234218000000000000)
      constant := (388876898848289291221647095000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree001.table
  base := (13478227027953774982485179783605788927409/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-171068292355830370327219245947644053000000000000)
      constant := (27530755505925351325273875363319034563804634785424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree001.table
  base := (4312130009912606491290344567179189067631/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-171110545202020051489874009705432178000000000000)
      constant := (27525027501691389062661140379564071219273325337550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49913435199935546641/100000000000000000000)
  directionHi := (24956717599967773321/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree002.table
  base := (62971538280636640704518429057529006495649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-332641486071323549072529665179122528000000000000)
      constant := (16231460123279393891459327795336364669223776884258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree002.table
  base := (125896482339884371933711478351067921521043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-332725991763702911397839192694698778000000000000)
      constant := (16225614177730112826015676804636510998950353426403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49913435199935546641/100000000000000000000)
  centralHi := (24956717599967773321/50000000000000000000)
  directionLo := (70588257004379487127/100000000000000000000)
  directionHi := (8823532125547435891/12500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree003.table
  base := (78025481327729228813164294889295567333513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-54912742198535191979760009378955667000000000000)
      constant := (1149287143966238102937851451755563394924673443697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree003.table
  base := (38994175488360276925920617205665623558787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-54926826480598419033978263964885042000000000000)
      constant := (1148784176109879060388463727641032175165610710006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70588257004379487127/100000000000000000000)
  centralHi := (8823532125547435891/12500000000000000000)
  directionLo := (17290521149317037967/20000000000000000000)
  directionHi := (21613151436646297459/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree004.table
  base := (12813900729018590424349469147534180200511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-655787873502309906563150503642079478000000000000)
      constant := (7236321631035945660649846903208205208964827268924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree004.table
  base := (25614090374746773766675461129322211636073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-655956884887068631213769558673231978000000000000)
      constant := (7233190023163981521775471395549903311970083174066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17290521149317037967/20000000000000000000)
  centralHi := (21613151436646297459/25000000000000000000)
  directionLo := (49913435199935546641/50000000000000000000)
  directionHi := (99826870399871093283/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree005.table
  base := (1415258995810181346376828131765328543261/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-817361067217803085308460922873557953000000000000)
      constant := (5603145934084320043218935657311738837478653499525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree005.table
  base := (7072279690386181746994496802207269953327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-817572331448751491121734741662498578000000000000)
      constant := (5601153085642115726103795037783916715547959451835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49913435199935546641/50000000000000000000)
  centralHi := (99826870399871093283/100000000000000000000)
  directionLo := (55804917048793344467/50000000000000000000)
  directionHi := (22321966819517337787/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree006.table
  base := (25280086325644305225068602038924067625621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-108770473437032918228196815789448492000000000000)
      constant := (532352544288417877474111880231145849621222089949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree006.table
  base := (25264998984444741152217143816676134236217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-108798642001159372336633324961307242000000000000)
      constant := (532229245604564019805201750387325581051518640673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55804917048793344467/50000000000000000000)
  centralHi := (22321966819517337787/20000000000000000000)
  directionLo := (122262447549314949813/100000000000000000000)
  directionHi := (61131223774657474907/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree007.table
  base := (1836581726620885571459163695223353893317/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-1140507454648789442799081761336514903000000000000)
      constant := (4470887186556860361404474970298644089387152151570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree007.table
  base := (18353988537455076912080198390470577541259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-1140803224572117210937665107641031778000000000000)
      constant := (4470484854692407401337679315849969928606487214939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122262447549314949813/100000000000000000000)
  centralHi := (61131223774657474907/50000000000000000000)
  directionLo := (26411707323993391579/20000000000000000000)
  directionHi := (16507317077495869737/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree008.table
  base := (3328165311093263929350885200123677419691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-1302080648364282621544392180567993378000000000000)
      constant := (4473300516246799156774392404008502902915105560044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree008.table
  base := (6651483747240726936276958939583534343643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-1302418671133800070845630290630298378000000000000)
      constant := (4473507075339022633216002638620416270619201202006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26411707323993391579/20000000000000000000)
  centralHi := (16507317077495869737/12500000000000000000)
  directionLo := (28235302801751794851/20000000000000000000)
  directionHi := (8823532125547435891/6250000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree009.table
  base := (9423474346857482703800657367638768202457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-162628204675530644476633622199941317000000000000)
      constant := (523285311889039508687739732863663898729867335233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree009.table
  base := (4707615859749350267488035758994057479257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-162670457521720325639288385957729442000000000000)
      constant := (523371204177653680422935729764559150803986228866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28235302801751794851/20000000000000000000)
  centralHi := (8823532125547435891/6250000000000000000)
  directionLo := (37435076399951659981/25000000000000000000)
  directionHi := (5989612223992265597/4000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree010.table
  base := (3158983920109114536231996677394814872753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-1625227035795268979035013019030950328000000000000)
      constant := (5131224484211274472754716433394484814169127554626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree010.table
  base := (252430963412171563087859303117369075643/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-1625649564257165790661560656608831578000000000000)
      constant := (5132557455190458252409300090869318442957699325075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37435076399951659981/25000000000000000000)
  centralHi := (5989612223992265597/4000000000000000000)
  directionLo := (7892007053750910173/5000000000000000000)
  directionHi := (157840141075018203461/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree011.table
  base := (1888935072763606294941170139024989567533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-1786800229510762157780323438262428803000000000000)
      constant := (5710453685866889491017823337137054226272325475386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree011.table
  base := (3771490649533957520136182782682237437013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-1787265010818848650569525839598098178000000000000)
      constant := (5712361429962750136368344311339901831656078416773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7892007053750910173/5000000000000000000)
  centralHi := (157840141075018203461/100000000000000000000)
  directionLo := (165544136555904067731/100000000000000000000)
  directionHi := (41386034138976016933/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree012.table
  base := (834842976423070559142736541587780845207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-216485935914028370725070428610434142000000000000)
      constant := (714471396291477585199911030841720889206187919966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree012.table
  base := (1663980838543786646039577288348319579639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-216542273042281278941943446954151642000000000000)
      constant := (714750221100922799796850112903163340113697198991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165544136555904067731/100000000000000000000)
  centralHi := (41386034138976016933/25000000000000000000)
  directionLo := (17290521149317037967/10000000000000000000)
  directionHi := (172905211493170379671/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree013.table
  base := (-9416140879388039594321021390121702517/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-2109946616941748515270944276725385753000000000000)
      constant := (7279430222328108270776567947008594142092489916430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree013.table
  base := (-49640343380795290376244081255372502647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-2110495903942214370385456205576631378000000000000)
      constant := (7282574772686769098741556349092833816682179587826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17290521149317037967/10000000000000000000)
  centralHi := (172905211493170379671/100000000000000000000)
  directionLo := (89982724973958394813/50000000000000000000)
  directionHi := (179965449947916789627/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree014.table
  base := (-157514503893893493557794846361596566849/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-2271519810657241694016254695956864228000000000000)
      constant := (8250182427674582278032963546719567164198852626710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree014.table
  base := (-789870095945082266465444028465105584959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-2272111350503897230293421388565897978000000000000)
      constant := (8253998972762033707328978402785125439654460634722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89982724973958394813/50000000000000000000)
  centralHi := (179965449947916789627/100000000000000000000)
  directionLo := (46689743378775324503/25000000000000000000)
  directionHi := (186758973515101298013/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree015.table
  base := (-2818957043991284700548406823651570452767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-270343667152526096973507235020926967000000000000)
      constant := (1037408456791680239552060383999177246054662762377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree015.table
  base := (-705769031135262355947661195958884752529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-270414088562842232244598507950573842000000000000)
      constant := (1037911473253600550915431233581292304410664730396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46689743378775324503/25000000000000000000)
  centralHi := (186758973515101298013/100000000000000000000)
  directionLo := (193313903281353441673/100000000000000000000)
  directionHi := (96656951640676720837/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree016.table
  base := (-3861062483470380770941180877225607211939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-2594666198088228051506875534419821178000000000000)
      constant := (10534391551552213529851979121990548354761924480781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree016.table
  base := (-966186652270172512012059771699021994069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-2595342243627262950109351754544431178000000000000)
      constant := (10539668794946815965470063377704659579453574644204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193313903281353441673/100000000000000000000)
  centralHi := (96656951640676720837/50000000000000000000)
  directionLo := (39930748159948437313/20000000000000000000)
  directionHi := (99826870399871093283/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree017.table
  base := (-4729827672455511431156317755654051461597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-2756239391803721230252185953651299653000000000000)
      constant := (11839713702616986665121847965826831933703055230963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree017.table
  base := (-4733114230206492291062576733269545528273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-2756957690188945810017316937533697778000000000000)
      constant := (11845781008821937998238034647303731965898140376767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39930748159948437313/20000000000000000000)
  centralHi := (99826870399871093283/50000000000000000000)
  directionLo := (205798365466756811823/100000000000000000000)
  directionHi := (12862397841672300739/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree018.table
  base := (-5448390034745699085854454932332015707309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-324201398391023823221944041431419792000000000000)
      constant := (1472188210648719172023902317673597308848850024779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree018.table
  base := (-340707128417871687764178123295207478941/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-324285904083403185547253568946996042000000000000)
      constant := (1472954614756720607676406835745701109330103983536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205798365466756811823/100000000000000000000)
  centralHi := (12862397841672300739/6250000000000000000)
  directionLo := (211764771013138461383/100000000000000000000)
  directionHi := (26470596376642307673/12500000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree019.table
  base := (-3017927551051278699893960564625458859231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-3079385779234707587742806792114256603000000000000)
      constant := (14761897293189457324281376941074607463094602939298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree019.table
  base := (-754806216695821515424258447327842503097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-3080188583312311529833247303512230978000000000000)
      constant := (14769665768566309448999056130410627583054968875704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211764771013138461383/100000000000000000000)
  centralHi := (26470596376642307673/12500000000000000000)
  directionLo := (217567619961484922237/100000000000000000000)
  directionHi := (108783809980742461119/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree020.table
  base := (-6508117849308721469750038756771885160067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-3240958972950200766488117211345735078000000000000)
      constant := (16374298214907385332197292981243718715163733058093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree020.table
  base := (-406900902396299191637774247255942304113/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-3241804029873994389741212486501497578000000000000)
      constant := (16382978266140902167418222455571331243609515586032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217567619961484922237/100000000000000000000)
  centralHi := (108783809980742461119/50000000000000000000)
  directionLo := (55804917048793344467/25000000000000000000)
  directionHi := (223219668195173377869/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree021.table
  base := (-6878461964250364622321625995827109039297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-378059129629521549470380847841912617000000000000)
      constant := (2009467085289283707594864420129695324003376838807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree021.table
  base := (-6880489985903545747851003093609566042051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-378157719603964138849908629943418242000000000000)
      constant := (2010537374509725244463115011259765231827896733381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55804917048793344467/25000000000000000000)
  centralHi := (223219668195173377869/100000000000000000000)
  directionLo := (45746418999795584927/20000000000000000000)
  directionHi := (57183023749744481159/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree022.table
  base := (-357900934764331115106919608476979802659/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-3564105360381187123978738049808692028000000000000)
      constant := (19893195368056444457441451253792548622132143913220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree022.table
  base := (-286392226474832472366491757174955267733/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-3565034922997360109557142852480030778000000000000)
      constant := (19903821748819642718980627500977702105328606452675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45746418999795584927/20000000000000000000)
  centralHi := (57183023749744481159/25000000000000000000)
  directionLo := (29264345386087900183/12500000000000000000)
  directionHi := (46822952617740640293/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree023.table
  base := (-3678065238383370927927267876627163797669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-3725678554096680302724048469040170503000000000000)
      constant := (21797082402222747872397482084385745404949102770902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree023.table
  base := (-7357701873463797682203629563887309198969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-3726650369559042969465108035469297378000000000000)
      constant := (21808744045134218028049479844896745512086099008151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29264345386087900183/12500000000000000000)
  centralHi := (46822952617740640293/20000000000000000000)
  directionLo := (119688212984338804363/50000000000000000000)
  directionHi := (239376425968677608727/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree024.table
  base := (-748064576543980893622237897655402071683/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-431916860868019275718817654252405442000000000000)
      constant := (2643984961204095269141759832414079512020186055730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree024.table
  base := (-1870506257425904200925365737389225746921/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-432029535124525092152563690939840442000000000000)
      constant := (2645400366803468256653848411989480186577789641404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119688212984338804363/50000000000000000000)
  centralHi := (239376425968677608727/100000000000000000000)
  directionLo := (244524895098629899627/100000000000000000000)
  directionHi := (61131223774657474907/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree025.table
  base := (-942270199945360047960287123241787599297/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-4048824941527666660214669307503127453000000000000)
      constant := (25888701377309198594347344757335458913974464314104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree025.table
  base := (-7539370144279357629526982378880749964059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-4049881262682408689281038401447830578000000000000)
      constant := (25902559038535078310566329473930081521959625706261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244524895098629899627/100000000000000000000)
  centralHi := (61131223774657474907/25000000000000000000)
  directionLo := (249567175999677733207/100000000000000000000)
  directionHi := (31195896999959716651/12500000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree026.table
  base := (-7534224943462423044595193979625852565537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-4210398135243159838959979726734605928000000000000)
      constant := (28074885668069073713155693935254171350501212538223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree026.table
  base := (-7535282217039592682970541447022821101589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-4211496709244091549189003584437097178000000000000)
      constant := (28089904593831163178047630556175510335102602323131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249567175999677733207/100000000000000000000)
  centralHi := (31195896999959716651/12500000000000000000)
  directionLo := (63627395018730083967/25000000000000000000)
  directionHi := (254509580074920335869/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree027.table
  base := (-7473500726895697802661138339940540198417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-485774592106517001967254460662898267000000000000)
      constant := (3372647001930317698987593911448557716870371747527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree027.table
  base := (-7474424301450598257177433498429658042049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-485901350645086045455218751936262642000000000000)
      constant := (3374449522277024704369317877426018216512377053719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63627395018730083967/25000000000000000000)
  centralHi := (254509580074920335869/100000000000000000000)
  directionLo := (129678908619877784753/50000000000000000000)
  directionHi := (259357817239755569507/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree028.table
  base := (-294396501696588273534618369019149490347/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-4533544522674146196450600565197562878000000000000)
      constant := (32725013396617943898068931694526321379595087555325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree028.table
  base := (-7360718221458624301731737935783892731617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-4534727602367457269004933950415630378000000000000)
      constant := (32742482555312451478573852099443396266981884730543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129678908619877784753/50000000000000000000)
  centralHi := (259357817239755569507/100000000000000000000)
  directionLo := (264117073239933915791/100000000000000000000)
  directionHi := (16507317077495869737/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree029.table
  base := (-7196760675891230296076569106855107971369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-4695117716389639375195910984429041353000000000000)
      constant := (35188036212353093062121543340111576520040760187751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree029.table
  base := (-224920706689564831044560121080337188741/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-4696343048929140128912899133404896978000000000000)
      constant := (35206794774972037377827027398580240482167452318048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264117073239933915791/100000000000000000000)
  centralHi := (16507317077495869737/6250000000000000000)
  directionLo := (268792074641881472689/100000000000000000000)
  directionHi := (26879207464188147269/10000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree030.table
  base := (-1397364246869509854630864507959478013267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-539632323345014728215691267073391092000000000000)
      constant := (4193615297030769833234343465652451412776775189385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree030.table
  base := (-3493716031589553728293512863788445248789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-539773166165646998757873812932684842000000000000)
      constant := (4195847640253204122107148691917759780059801429318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268792074641881472689/100000000000000000000)
  centralHi := (26879207464188147269/10000000000000000000)
  directionLo := (68346785953942699777/25000000000000000000)
  directionHi := (273387143815770799109/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree031.table
  base := (-3366214727073534180670804879071176880517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-5018264103820625732686531822891998303000000000000)
      constant := (40388220173315403419121477274471576302205006507286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree031.table
  base := (-3366480204575431211912501956563612821343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-5019573942052505848728829499383430178000000000000)
      constant := (40409687089068475362824742130021050590585893634594) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68346785953942699777/25000000000000000000)
  centralHi := (273387143815770799109/100000000000000000000)
  directionLo := (277906245732626726711/100000000000000000000)
  directionHi := (34738280716578340839/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree032.table
  base := (-321777487090559346688870005527725067637/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-5179837297536118911431842242123476778000000000000)
      constant := (43124833365513568366997424792743933790210256882460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree032.table
  base := (-51488086299911957875011834895827631623/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-5181189388614188708636794682372696778000000000000)
      constant := (43147719570365927478576305256547813955017147677125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277906245732626726711/100000000000000000000)
  centralHi := (34738280716578340839/12500000000000000000)
  directionLo := (282353028017517948511/100000000000000000000)
  directionHi := (8823532125547435891/3125000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree033.table
  base := (-1524458643516835227048396242598420580329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-593490054583512454464128073483883917000000000000)
      constant := (5105796295080429089661238959873486342329103137596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree033.table
  base := (-3049117262165621234875071190662884749217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-593644981686207952060528873929107042000000000000)
      constant := (5108501750961837005512437571041468370847129324654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282353028017517948511/100000000000000000000)
  centralHi := (8823532125547435891/3125000000000000000)
  directionLo := (286730855409946141493/100000000000000000000)
  directionHi := (143365427704973070747/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree034.table
  base := (-1430168508992466686506344799606414134787/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-5502983684967105268922463080586433728000000000000)
      constant := (48870042889392639732691593188006114511602382835892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree034.table
  base := (-2860510334165710413396765186936268994901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-5504420281737554428452725048351229978000000000000)
      constant := (48895898631467106864792476206792348300449350631158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286730855409946141493/100000000000000000000)
  centralHi := (143365427704973070747/50000000000000000000)
  directionLo := (72760709889325573661/25000000000000000000)
  directionHi := (58208567911460458929/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree035.table
  base := (-5305237488491245820498201519766461631821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-5664556878682598447667773499817912203000000000000)
      constant := (51878313041378971078870736401987477345633839760259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree035.table
  base := (-1326384412744651990374165122105476406807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-5666035728299237288360690231340496578000000000000)
      constant := (51905719282111496509030676412545656562147604666212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72760709889325573661/25000000000000000000)
  centralHi := (58208567911460458929/20000000000000000000)
  directionLo := (295291864891391429273/100000000000000000000)
  directionHi := (147645932445695714637/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree036.table
  base := (-4852508617701805236419058720597517992287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-647347785822010180712564879894376742000000000000)
      constant := (6108539083248207427364938769390798176248675383497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree036.table
  base := (-2426384163972427027004298443003099773973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-647516797206768905363183934925529242000000000000)
      constant := (6111761383774214714464446445913843491353361037126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295291864891391429273/100000000000000000000)
  centralHi := (147645932445695714637/50000000000000000000)
  directionLo := (37435076399951659981/12500000000000000000)
  directionHi := (299480611199613279849/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree037.table
  base := (-1090828729404646457706587215895718755027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-5987703266113584805158394338280869153000000000000)
      constant := (58165553555861176950741444171085873465915780895732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree037.table
  base := (-1090884863474620550390360312176221756623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-5989266621422603008176620597319029778000000000000)
      constant := (58196192784163989682209811080438287128210692225668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37435076399951659981/12500000000000000000)
  centralHi := (299480611199613279849/100000000000000000000)
  directionLo := (303611573392636170647/100000000000000000000)
  directionHi := (37951446674079521331/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree038.table
  base := (-59974257674173919374431668893037322989/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-6149276459829077983903704757512347628000000000000)
      constant := (61444329748847846442883581183833168544779868718784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree038.table
  base := (-3838546475466381564711999071364051098987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-6150882067984285868084585780308296378000000000000)
      constant := (61476651643923763191000283115022401197223375160773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303611573392636170647/100000000000000000000)
  centralHi := (37951446674079521331/12500000000000000000)
  directionLo := (307687078882767296473/100000000000000000000)
  directionHi := (153843539441383648237/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree039.table
  base := (-1639103456404912430601635871801235260481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-701205517060507906961001686304869567000000000000)
      constant := (7201456189076231531230527928429941824886910037422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree039.table
  base := (-163918719311122777807200987156134627669/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-701388612727329858665838995921951442000000000000)
      constant := (7205239386752935497747991822538026498709097678780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307687078882767296473/100000000000000000000)
  centralHi := (153843539441383648237/50000000000000000000)
  directionLo := (62341860583357128307/20000000000000000000)
  directionHi := (4870457858074775649/1562500000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree040.table
  base := (-2683370778721128558528654191917007097843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-6472422847260064341394325595975304578000000000000)
      constant := (68271818637177823408202244028783517454683092260797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree040.table
  base := (-2683515269287028438193582546566842535011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-6474112961107651587900516146286829578000000000000)
      constant := (68307638582900645998399427986948446379170702408269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62341860583357128307/20000000000000000000)
  centralHi := (4870457858074775649/1562500000000000000)
  directionLo := (315680282150036406921/100000000000000000000)
  directionHi := (157840141075018203461/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree041.table
  base := (-410851693977007775975686707809121221501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-6633996040975557520139636015206783053000000000000)
      constant := (71820415745977642446141398635856644005573923284895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree041.table
  base := (-2054383053691752432234308859063276094847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-6635728407669334447808481329276096178000000000000)
      constant := (71858051198551062930767904849731288082229758057713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315680282150036406921/100000000000000000000)
  centralHi := (157840141075018203461/50000000000000000000)
  directionLo := (319601926702241204401/100000000000000000000)
  directionHi := (159800963351120602201/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree042.table
  base := (-11129748570581843625590404166847800091/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-755063248299005633209438492715362392000000000000)
      constant := (8384316955986693842566682613728196242554153077625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree042.table
  base := (-1391325927063011849855720289318928468209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-755260428247890811968494056918373642000000000000)
      constant := (8388705328240774497826427825523864991991249432679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319601926702241204401/100000000000000000000)
  centralHi := (159800963351120602201/50000000000000000000)
  directionLo := (40434503862195721163/12500000000000000000)
  directionHi := (64695206179513153861/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree043.table
  base := (-694544319258300208919943203613706290071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-6957142428406543877630256853669740003000000000000)
      constant := (79187091840415218609413024340393948091227334562009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree043.table
  base := (-694636776871389742534594521087028532303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-6958959300792700167624411695254629378000000000000)
      constant := (79228491523723635700572242882702568439472908047137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40434503862195721163/12500000000000000000)
  centralHi := (64695206179513153861/20000000000000000000)
  directionLo := (163652141430154442927/50000000000000000000)
  directionHi := (65460856572061777171/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree044.table
  base := (4439701315153240216652180119994900243/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-7118715622122037056375567272901218478000000000000)
      constant := (83005102018845072068338295764636236807793689516824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree044.table
  base := (8859506658877370259500862561664545729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-7120574747354383027532376878243895978000000000000)
      constant := (83048450509421974738721187266572818675997911255236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163652141430154442927/50000000000000000000)
  centralHi := (65460856572061777171/20000000000000000000)
  directionLo := (331088273111808135463/100000000000000000000)
  directionHi := (41386034138976016933/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree045.table
  base := (798759709736871572325908422859406086369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-808920979537503359457875299125855217000000000000)
      constant := (9656984077111012457712717442127177656703863636361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree045.table
  base := (798691242434141529184591593687783560557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-809132243768451765271149117914795842000000000000)
      constant := (9662022055572303723726937514427271863452908854133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331088273111808135463/100000000000000000000)
  centralHi := (41386034138976016933/12500000000000000000)
  directionLo := (167414751146380033401/50000000000000000000)
  directionHi := (334829502292760066803/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree046.table
  base := (398751854637315612110884753754592552741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-7441862009553023413866188111364175428000000000000)
      constant := (90910333619705903386873010737069213827501343036244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree046.table
  base := (1594948544110620578796906583221231835481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-7443805640477748747348307244222429178000000000000)
      constant := (90957713279486575940218739946584567502607320406601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167414751146380033401/50000000000000000000)
  centralHi := (334829502292760066803/100000000000000000000)
  directionLo := (67705877623460604159/20000000000000000000)
  directionHi := (84632347029325755199/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree047.table
  base := (2424113893962653122270347106174756000313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-7603435203268516592611498530595653903000000000000)
      constant := (94997514082070719876864320607176668869515015196073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree047.table
  base := (606015823067402763815726351853394022089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-7605421087039431607256272427211695778000000000000)
      constant := (95046976159481921932816126470495684553749319029476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67705877623460604159/20000000000000000000)
  centralHi := (84632347029325755199/25000000000000000000)
  directionLo := (171094635825128769989/50000000000000000000)
  directionHi := (342189271650257539979/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree048.table
  base := (65719112178175995409767684844134637863/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-862778710776001085706312105536348042000000000000)
      constant := (11019375815401788880638432441319342122544693942350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree048.table
  base := (3285912137204226886148612570499270452597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-863004059289012718573804178911218042000000000000)
      constant := (11025107935584723447343321688035745299985480008893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171094635825128769989/50000000000000000000)
  centralHi := (342189271650257539979/100000000000000000000)
  directionLo := (345810422986340759341/100000000000000000000)
  directionHi := (172905211493170379671/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree049.table
  base := (2090214325057022088982248284181633654409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-7926581590699502950102119369058610853000000000000)
      constant := (103440925146476396441347010486384960114146592632178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree049.table
  base := (16329653593602871026892559622787839081/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-7928651980162797327072202793190228978000000000000)
      constant := (103494685838629666013038317136618586976033185843456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345810422986340759341/100000000000000000000)
  centralHi := (172905211493170379671/50000000000000000000)
  directionLo := (349394046399548826489/100000000000000000000)
  directionHi := (34939404639954882649/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree050.table
  base := (5107445603795816616736327952815777516503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-8088154784414996128847429788290089328000000000000)
      constant := (107797131365506202374247597254525400553875744921063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree050.table
  base := (255370678044394508901920202128712970141/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-8090267426724480186980167976179495578000000000000)
      constant := (107853108291531268140679139513989210023743932489220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349394046399548826489/100000000000000000000)
  centralHi := (34939404639954882649/10000000000000000000)
  directionLo := (352941285021897435639/100000000000000000000)
  directionHi := (8823532125547435891/2500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree051.table
  base := (242677317434088417926675681271849329817/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-916636442014498811954748911946840867000000000000)
      constant := (12471443513823080597046639707471171497849886476825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree051.table
  base := (6066905442332831602313313217051480790847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-916875874809573671876459239907640242000000000000)
      constant := (12477914380278953365458729685512565666698647173143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352941285021897435639/100000000000000000000)
  centralHi := (8823532125547435891/2500000000000000000)
  directionLo := (356453225103051084751/100000000000000000000)
  directionHi := (22278326568940692797/6250000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree052.table
  base := (3529414394014186926638423723063453767447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-8411301171845982486338050626753046278000000000000)
      constant := (116778498039870880717423146894138572061273251933774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree052.table
  base := (1764701301763493873852817585881404256879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-8413498319847845906796098342158028778000000000000)
      constant := (116839041361130598353091729630925347892450137891836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356453225103051084751/100000000000000000000)
  centralHi := (22278326568940692797/6250000000000000000)
  directionLo := (89982724973958394813/25000000000000000000)
  directionHi := (359930899895833579253/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree053.table
  base := (808308112401038777881691277976091838581/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (3538782)
      previous := (1769391)
      next := (1769391)
      square := (54338754646956000878277315676200000000000000)
      linear := (-3051931066415619674290979368453017000000000000)
      constant := (43219524378892372847504733862371462387495813890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree053.table
  base := (2020765226568662243133110894585891339041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (3538782)
      previous := (1769391)
      next := (1769391)
      square := (54338754646956000878277315676200000000000000)
      linear := (-3052728289928632526416540948788642000000000000)
      constant := (43241914377700323620793975986908720216643804516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89982724973958394813/25000000000000000000)
  centralHi := (359930899895833579253/100000000000000000000)
  directionLo := (363375293207013095813/100000000000000000000)
  directionHi := (181687646603506547907/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree054.table
  base := (9139646169884701313207514727137584768077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-970494173252996538203185718357333692000000000000)
      constant := (14013158207456331795154452400937498876442796125013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree054.table
  base := (913962884187633602196208327642047607011/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-970747690330134625179114300904062442000000000000)
      constant := (14020412470116080429276492489512556574213213448590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363375293207013095813/100000000000000000000)
  centralHi := (181687646603506547907/50000000000000000000)
  directionLo := (366787342647944849441/100000000000000000000)
  directionHi := (183393671323972424721/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree055.table
  base := (10228487102223391235171683008388992131037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-8896020752992462022573981884447481703000000000000)
      constant := (130922833007432150231480212806508565476367636587277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree055.table
  base := (159819879000090462362328453944020991607/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-8898344659532894486519993891125828578000000000000)
      constant := (130990560908907416291965401037569873142684756111808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366787342647944849441/100000000000000000000)
  centralHi := (183393671323972424721/50000000000000000000)
  directionLo := (370167942615509409891/100000000000000000000)
  directionHi := (92541985653877352473/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree056.table
  base := (2269914588895381396278451071911489628513/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-9057593946707955201319292303678960178000000000000)
      constant := (135816867453585577498255675049292092821167108441365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree056.table
  base := (5674780114401199288091216801546653691601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-9059960106094577346427959074115095178000000000000)
      constant := (135887079580074220949154007090449927565835792730242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370167942615509409891/100000000000000000000)
  centralHi := (92541985653877352473/25000000000000000000)
  directionLo := (14940717881208103841/4000000000000000000)
  directionHi := (186758973515101298013/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree057.table
  base := (12502877638598977664150284581694476694953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1024351904491494264451622524767826517000000000000)
      constant := (15644502653854468545156392831692820947398345927057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree057.table
  base := (3125716687797893330833824099358204655061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1024619505850695578481769361900484642000000000000)
      constant := (15652584992212123591905300913526248796809001861236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14940717881208103841/4000000000000000000)
  centralHi := (186758973515101298013/50000000000000000000)
  directionLo := (188419085927564273641/50000000000000000000)
  directionHi := (376838171855128547283/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree058.table
  base := (13688379264080099011714159655047442554519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-9380740334138941558809913142141917128000000000000)
      constant := (145873799507162996136590320302200815714683026783399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree058.table
  base := (3422092486234919693983446541966629702611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-9383190999217943066243889440093628378000000000000)
      constant := (145949114170216719180959973532484578956178094045324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188419085927564273641/50000000000000000000)
  centralHi := (376838171855128547283/100000000000000000000)
  directionLo := (4751617467711875801/1250000000000000000)
  directionHi := (380129397416950064081/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree059.table
  base := (7453029690491940585572643928974539916247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-9542313527854434737555223561373395603000000000000)
      constant := (151036691970990374522696568924139568364684710583374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree059.table
  base := (7453025703291013734838091227009129402011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-9544806445779625926151854623082894978000000000000)
      constant := (151114624955631510070350558564307790240756204597462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4751617467711875801/1250000000000000000)
  centralHi := (380129397416950064081/100000000000000000000)
  directionLo := (191696185273750118327/50000000000000000000)
  directionHi := (76678474109500047331/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree060.table
  base := (16155902477296927524639742552251306968521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1078209635729991990700059331178319342000000000000)
      constant := (17365466588810863447486343695612626482145135040049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree060.table
  base := (16155895655550068944455299505627681348249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1078491321371256531784424422896906842000000000000)
      constant := (17374421701476253664435350415795907438969353694081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191696185273750118327/50000000000000000000)
  centralHi := (76678474109500047331/20000000000000000000)
  directionLo := (193313903281353441673/50000000000000000000)
  directionHi := (386627806562706883347/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree061.table
  base := (8718947752014605482481661573296686868377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-9865459915285421095045844399836352553000000000000)
      constant := (161631319829102049082254736684740912170064633362834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree061.table
  base := (8718944834974284784741658654702846487583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-9868037338902991645967784989061428178000000000000)
      constant := (161714623583650903033104806855282906801814170267486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193313903281353441673/50000000000000000000)
  centralHi := (386627806562706883347/100000000000000000000)
  directionLo := (389836391093684398527/100000000000000000000)
  directionHi := (6091193610838818727/1562500000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree062.table
  base := (9376013742065906579782022633674189080229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-10027033109000914273791154819067831028000000000000)
      constant := (167063052161471398443624290496678145182526949576618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree062.table
  base := (9376011248030983737627368420775496197933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-10029652785464674505875750172050694778000000000000)
      constant := (167149108370767198423891133590209756755988597152186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389836391093684398527/100000000000000000000)
  centralHi := (6091193610838818727/1562500000000000000)
  directionLo := (49127347722908848389/12500000000000000000)
  directionHi := (393018781783270787113/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree063.table
  base := (10049144591755606389702771209564766936681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1132067366968489716948496137588812167000000000000)
      constant := (19176043902177655077451935409537756204319280518178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree063.table
  base := (20098284919880029710541065490021189812217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1132363136891817485087079483893329042000000000000)
      constant := (19185916500043076728378695114436419082322070984673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49127347722908848389/12500000000000000000)
  centralHi := (393018781783270787113/100000000000000000000)
  directionLo := (198087804929950436843/50000000000000000000)
  directionHi := (396175609859900873687/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree064.table
  base := (134229205214252213334850781149421295247/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-10350179496431900631281775657530787978000000000000)
      constant := (178195347713533199509122629650624314093770840109920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree064.table
  base := (671145912212272912048863645580617105247/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-10352883678588040225691680538029227978000000000000)
      constant := (178287042984762849407249661350060674496361432341984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198087804929950436843/50000000000000000000)
  centralHi := (396175609859900873687/100000000000000000000)
  directionLo := (399307481599484373131/100000000000000000000)
  directionHi := (99826870399871093283/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree065.table
  base := (22887171901952274011166216876016019100841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-10511752690147393810027086076762266453000000000000)
      constant := (183895909110509352333520563221209171265357479419161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree065.table
  base := (183097350313349661727867086591984511869/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-10514499125149723085599645721018494578000000000000)
      constant := (183990490993020936803809128788051072270128489093625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399307481599484373131/100000000000000000000)
  centralHi := (99826870399871093283/25000000000000000000)
  directionLo := (402414979684877928737/100000000000000000000)
  directionHi := (201207489842438964369/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree066.table
  base := (24329780889599031500871573265922592104777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1185925098206987443196932943999304992000000000000)
      constant := (21076230956665610728125164482529148276496708027313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree066.table
  base := (760305569713985351434484455022403924879/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1186234952412378438389734544889751242000000000000)
      constant := (21087065758472467461142357978246337949601598225632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402414979684877928737/100000000000000000000)
  centralHi := (201207489842438964369/50000000000000000000)
  directionLo := (405498664471584765481/100000000000000000000)
  directionHi := (202749332235792382741/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree067.table
  base := (12902247586553271439493895887581330876461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-10834899077578380167517706915225223403000000000000)
      constant := (195565855622672500060670148221776274762982155874362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree067.table
  base := (12902246451341557998268141258746246797649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-10837730018273088805415576086997027778000000000000)
      constant := (195666344896550306424937723819937749290867535568258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405498664471584765481/100000000000000000000)
  centralHi := (202749332235792382741/50000000000000000000)
  directionLo := (408559075167468340763/100000000000000000000)
  directionHi := (102139768791867085191/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree068.table
  base := (3413913857823484252009783087003952535943/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-10996472271293873346263017334456701878000000000000)
      constant := (201535239652822255452669354698900793457539064714424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree068.table
  base := (6827827231051641077089453309020475194639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-10999345464834771665323541269986294378000000000000)
      constant := (201638749709382376116855567295663875519790260823676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408559075167468340763/100000000000000000000)
  centralHi := (102139768791867085191/25000000000000000000)
  directionLo := (411596730933513623647/100000000000000000000)
  directionHi := (12862397841672300739/3125000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree069.table
  base := (7212556171450379219006489812335184231709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1239782829445485169445369750409797817000000000000)
      constant := (23066025587046703096185291353638802397249788395284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree069.table
  base := (7212555757815031683152762224571785943257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1240106767932939391692389605886173442000000000000)
      constant := (23077867316528798650260915861428619689353374121732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411596730933513623647/100000000000000000000)
  centralHi := (12862397841672300739/3125000000000000000)
  directionLo := (25913258244499976391/6250000000000000000)
  directionHi := (414612131911999622257/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree070.table
  base := (15210616945040335209006089310713435725687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-11319618658724859703753638172919658828000000000000)
      constant := (213742827163662673368818632866150474944909580099854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree070.table
  base := (7605308119528187545589017048335433333333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-11322576357958137385139471635964827578000000000000)
      constant := (213852512964760599969084381384054459278776230077972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25913258244499976391/6250000000000000000)
  centralHi := (414612131911999622257/100000000000000000000)
  directionLo := (26100360011740584317/6250000000000000000)
  directionHi := (417605760187849349073/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree071.table
  base := (32024336159834324711880345099222214270867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252810000000000000000000000000000000000000000
      center := (1971918)
      previous := (985959)
      next := (985959)
      square := (30279222734239120505272957693800000000000000)
      linear := (-2277562359143097179626849552102983000000000000)
      constant := (43638371354581799572048627002022711830231788627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree071.table
  base := (16012167477560958996123200928013269956137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252810000000000000000000000000000000000000000
      center := (1971918)
      previous := (985959)
      next := (985959)
      square := (30279222734239120505272957693800000000000000)
      linear := (-2278157469652810998819170168409858000000000000)
      constant := (43660755953787394798048875452115699955522198994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26100360011740584317/6250000000000000000)
  centralHi := (417605760187849349073/100000000000000000000)
  directionLo := (420578080688389781029/100000000000000000000)
  directionHi := (42057808068838978103/10000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree072.table
  base := (33659529547147637155223218928548095391221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1293640560683982895693806556820290642000000000000)
      constant := (25145426504391959151952970315578119104367810476349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree072.table
  base := (8414882129868168991617614028449273959037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1293978583453500344995044666882595642000000000000)
      constant := (25158319888445429632414297858136970532749051989012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420578080688389781029/100000000000000000000)
  centralHi := (42057808068838978103/10000000000000000000)
  directionLo := (423529542026276922767/100000000000000000000)
  directionHi := (26470596376642307673/6250000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree073.table
  base := (2207925775837604882819971834444137800671/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-11804338239871339239989569430614094253000000000000)
      constant := (232726252578076926812920404575310279755898962969456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree073.table
  base := (7065362307383377756508223925558109065593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-11807422697643185964863367184932627378000000000000)
      constant := (232845537455389360456465697119485904485015303434765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423529542026276922767/100000000000000000000)
  centralHi := (26470596376642307673/6250000000000000000)
  directionLo := (213230288644956602817/50000000000000000000)
  directionHi := (85292115457982641127/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree074.table
  base := (370261833801628761579320900560689380957/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-11965911433586832418734879849845572728000000000000)
      constant := (239233271938425064033940017060414605108145851559700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree074.table
  base := (37026182632765639010605440270251133434301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-11969038144204868824771332367921893978000000000000)
      constant := (239355845965991291932071559317373372818841273011821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213230288644956602817/50000000000000000000)
  centralHi := (85292115457982641127/20000000000000000000)
  directionLo := (429371604785300398253/100000000000000000000)
  directionHi := (214685802392650199127/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree075.table
  base := (19378820643935153782116745156512028678399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1347498291922480621942243363230783467000000000000)
      constant := (27314432941421759580387779677714650160269202978862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree075.table
  base := (38757640650665158365975879783872160809569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1347850398974061298297699727879017842000000000000)
      constant := (27328422708938575341584902936848698296458673857161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429371604785300398253/100000000000000000000)
  centralHi := (214685802392650199127/50000000000000000000)
  directionLo := (432263028732925949177/100000000000000000000)
  directionHi := (216131514366462974589/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree076.table
  base := (40521185161082678415081974243552152261039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-12289057821017818776225500688308529678000000000000)
      constant := (252516126056877521237057998853975138029970399200319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree076.table
  base := (20260592308960044223055786216204556638087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-12292269037328234544587262733900427178000000000000)
      constant := (252645412574795242938583460268196854318176907620654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432263028732925949177/100000000000000000000)
  centralHi := (216131514366462974589/50000000000000000000)
  directionLo := (217567619961484922237/50000000000000000000)
  directionHi := (17405409596918793779/4000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree077.table
  base := (42316814179243442204518496629817109900009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-12450631014733311954970811107540008153000000000000)
      constant := (259291960586097144721417306037775654313012554873689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree077.table
  base := (1057920342908105134696338057880001580761/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-12453884483889917404495227916889693778000000000000)
      constant := (259424670444762040864242082524635960808383447099240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217567619961484922237/50000000000000000000)
  centralHi := (17405409596918793779/4000000000000000000)
  directionLo := (218994308165919402763/50000000000000000000)
  directionHi := (437988616331838805527/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree078.table
  base := (44144527652087876201828898099724906149631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1401356023160978348190680169641276292000000000000)
      constant := (29573044441387368946569161418246370322462914247639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree078.table
  base := (44144527257623897247639771221436696504019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1401722214494622251600354788875440042000000000000)
      constant := (29588175322515053856823187898759083771298618219211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218994308165919402763/50000000000000000000)
  centralHi := (437988616331838805527/100000000000000000000)
  directionLo := (44082352370278160929/10000000000000000000)
  directionHi := (440823523702781609291/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree079.table
  base := (46004324998955060017202492508132668417211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-12773777402164298312461431946002965103000000000000)
      constant := (273112444142044737750436052288909539351909282417931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree079.table
  base := (5750540582859825874767587309849909687773/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-12777115377013283124311158282868226978000000000000)
      constant := (273252134874634509323933160533950764015579409781864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44082352370278160929/10000000000000000000)
  centralHi := (440823523702781609291/100000000000000000000)
  directionLo := (110910079023277632009/25000000000000000000)
  directionHi := (443640316093110528037/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree080.table
  base := (23948102865692365342119213517297451870667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-12935350595879791491206742365234443578000000000000)
      constant := (280157093032522277554860008032717560141644195529014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree080.table
  base := (47896205445099313814399312230003633831007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-12938730823574965984219123465857493578000000000000)
      constant := (280300341298696493177582297058116081170950589041647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110910079023277632009/25000000000000000000)
  centralHi := (443640316093110528037/100000000000000000000)
  directionLo := (55804917048793344467/12500000000000000000)
  directionHi := (446439336390346755737/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree081.table
  base := (12455042359619359261817907991061936823733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1455213754399476074439116976051769117000000000000)
      constant := (31921260732394809877672350638289789781096779963508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree081.table
  base := (49820169194644425106184383959596821324143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1455594030015183204903009849871862242000000000000)
      constant := (31937577458068454294199411461957756688812668660167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55804917048793344467/12500000000000000000)
  centralHi := (446439336390346755737/100000000000000000000)
  directionLo := (112305229199854979943/25000000000000000000)
  directionHi := (449220916799419919773/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree082.table
  base := (51776215774579232950803807925647141771689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-13258496983310777848697363203697400528000000000000)
      constant := (294515204775087107145300689639771008387061680898969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree082.table
  base := (51776215566935139290913420451479027857469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-13261961716698331704035053831836026778000000000000)
      constant := (294665702302479649156528858789030009355757220570349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112305229199854979943/25000000000000000000)
  centralHi := (449220916799419919773/100000000000000000000)
  directionLo := (903970758605762687/200000000000000000)
  directionHi := (451985379302881343501/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree083.table
  base := (53764344448921815695279697258580960764711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-13420070177026271027442673622928879003000000000000)
      constant := (301828667546067777538988881658441926641277342965431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree083.table
  base := (1344108606803047354335337444400278257501/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-13423577163260014563943019014825293378000000000000)
      constant := (301982856801348305636447827668736171807366283960840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (903970758605762687/200000000000000000)
  centralHi := (451985379302881343501/100000000000000000000)
  directionLo := (454733036095935835651/100000000000000000000)
  directionHi := (113683259023983958913/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree084.table
  base := (55784555216907621380631718622212017493989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1509071485637973800687553782462261942000000000000)
      constant := (34359081652591490500421825247972594699545840724141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree084.table
  base := (13946138766598005942851329773380134447589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1509465845535744158205664910868284442000000000000)
      constant := (34376628954238911232856108573408881048082327530164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454733036095935835651/100000000000000000000)
  centralHi := (113683259023983958913/25000000000000000000)
  directionLo := (457464189997955849271/100000000000000000000)
  directionHi := (57183023749744481159/12500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree085.table
  base := (11567369574555737702895869225371224858601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-13743216564457257384933294461391835953000000000000)
      constant := (316724406730631910469274922229544054265096856860605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree085.table
  base := (57836847744657961998165513772804925540903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-13746808056383380283758949380803826578000000000000)
      constant := (316886113636748664174020263005374127902224426033463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457464189997955849271/100000000000000000000)
  centralHi := (57183023749744481159/12500000000000000000)
  directionLo := (460179134842013467563/100000000000000000000)
  directionHi := (115044783710503366891/25000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree086.table
  base := (29960611121724786569503600945887184027983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-13904789758172750563678604880623314428000000000000)
      constant := (324306683095934993194480115057502908858741120164286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree086.table
  base := (11984244426881346126232514583932193970239/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-13908423502945063143666914563793093178000000000000)
      constant := (324472215925158378534474393238916467560171434467595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460179134842013467563/100000000000000000000)
  centralHi := (115044783710503366891/25000000000000000000)
  directionLo := (462878155843848585271/100000000000000000000)
  directionHi := (57859769480481073159/12500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree087.table
  base := (620376781833194856497443883253468260459/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1562929216876471526935990588872754767000000000000)
      constant := (36886507105630786288157471791813181807704795757100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree087.table
  base := (31018839045263136452314665376638835070219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1563337661056305111508319971864706642000000000000)
      constant := (36905329714987338105266628835815693542114855814022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462878155843848585271/100000000000000000000)
  centralHi := (57859769480481073159/12500000000000000000)
  directionLo := (232780764975792374357/50000000000000000000)
  directionHi := (93112305990316949743/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree088.table
  base := (2005819236559630219020717081889621459667/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-14227936145603736921169225719086271378000000000000)
      constant := (339740049279249090161806035525088351752894484272224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree088.table
  base := (32093107745476743571012009517417844950803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-14231654396068428863482844929771626378000000000000)
      constant := (339913368150375750077159928891263823370145008982726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232780764975792374357/50000000000000000000)
  centralHi := (93112305990316949743/20000000000000000000)
  directionLo := (468229526177406402929/100000000000000000000)
  directionHi := (46822952617740640293/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree089.table
  base := (66366834300184709744557470122018704758761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-14389509339319230099914536138317749853000000000000)
      constant := (347591139068520618341505802526260187230187689915481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree089.table
  base := (66366834233013455513169265189257216591547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-14393269842630111723390810112760892978000000000000)
      constant := (347768418058542452226927377284932608909653185422987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468229526177406402929/100000000000000000000)
  centralHi := (46822952617740640293/10000000000000000000)
  directionLo := (470882405912321885299/100000000000000000000)
  directionHi := (4708824059123218853/1000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree090.table
  base := (8572441785934912110081036937837780595091/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1616786948114969253184427395283247592000000000000)
      constant := (39503537034160703092467125017059498631866273043032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree090.table
  base := (4286220889396255635571703762250422352017/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1617209476576866064810975032861128842000000000000)
      constant := (39523679683153280422046255657531448343215011373968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470882405912321885299/100000000000000000000)
  centralHi := (4708824059123218853/1000000000000000000)
  directionLo := (236760211612527305191/50000000000000000000)
  directionHi := (473520423225054610383/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree091.table
  base := (35412157729442651073192786895582193812271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-14712655726750216457405156976780706803000000000000)
      constant := (363562131986734887291003573147684598756186459408382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree091.table
  base := (70824315410285854228857394113302037566491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-14716500735753477443206740478739426178000000000000)
      constant := (363747465410628652194595641904806647272872751672811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236760211612527305191/50000000000000000000)
  centralHi := (473520423225054610383/100000000000000000000)
  directionLo := (238071912573014901277/50000000000000000000)
  directionHi := (95228765029205960511/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree092.table
  base := (14620235550614778220704746873937216622403/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-14874228920465709636150467396012185278000000000000)
      constant := (371682035098570456775936950417672495125327604974815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree092.table
  base := (73101177711742881200809765771972511357897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-14878116182315160303114705661728692778000000000000)
      constant := (371871462837502157964724993684864672893640169041337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238071912573014901277/50000000000000000000)
  centralHi := (95228765029205960511/20000000000000000000)
  directionLo := (119688212984338804363/25000000000000000000)
  directionHi := (478752851937355217453/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree093.table
  base := (37705060559227812798022356502230886765607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1670644679353466979432864201693740417000000000000)
      constant := (42210171404042044424540653283785255211522967015166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree093.table
  base := (18852530270827538305054893355528969347461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1671081292097427018113630093857551042000000000000)
      constant := (42231678824716601912352000976140677892423469923636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119688212984338804363/25000000000000000000)
  centralHi := (478752851937355217453/100000000000000000000)
  directionLo := (120336934337407745289/25000000000000000000)
  directionHi := (481347737349630981157/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree094.table
  base := (12440183281861435797524916544036989623/1600000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-15197375307896695993641088234475142228000000000000)
      constant := (388190654594628196395677954704155684715227103643750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree094.table
  base := (77751145481751775912829633556448822818813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-15201347075438526022930636027707225978000000000000)
      constant := (388388405159960381793074008494666631720689036134573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120336934337407745289/25000000000000000000)
  centralHi := (481347737349630981157/100000000000000000000)
  directionLo := (96785741773273091367/20000000000000000000)
  directionHi := (120982177216591364209/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree095.table
  base := (80124250896104376132366107161980811871873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-15358948501612189172386398653706620703000000000000)
      constant := (396579370968667649928708047408037903529797602238833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree095.table
  base := (10015531358837514619373612105933684226139/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-15362962522000208882838601210696492578000000000000)
      constant := (396781350045400305331948138813523399028302896939352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96785741773273091367/20000000000000000000)
  centralHi := (120982177216591364209/25000000000000000000)
  directionLo := (60811998492090057839/12500000000000000000)
  directionHi := (486495987936720462713/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree096.table
  base := (41264718620579939259153894275453337779469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1724502410591964705681301008104233242000000000000)
      constant := (45006410194953713273594610604940598961142731540522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree096.table
  base := (40297576767365682740167141675274057813/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1104493182)
      previous := (552246591)
      next := (552246591)
      square := (16959729089255489607453442192716200000000000000)
      linear := (-1724953107617987971416285154853973242000000000000)
      constant := (45029327119430079867600228646139503133333197613056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60811998492090057839/12500000000000000000)
  centralHi := (486495987936720462713/100000000000000000000)
  directionLo := (244524895098629899627/50000000000000000000)
  directionHi := (97809958039451959851/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree097.table
  base := (84966704520970531720536557614592043106233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-15682094889043175529877019492169577653000000000000)
      constant := (413625616949083696986798967722876214984737148100393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree097.table
  base := (21241676125653917073776174100397224053313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-15686193415123574602654531576675025778000000000000)
      constant := (413836187245092486699704253470940622141127975236292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell157.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244524895098629899627/50000000000000000000)
  centralHi := (97809958039451959851/20000000000000000000)
  directionLo := (491590325683329524677/100000000000000000000)
  directionHi := (245795162841664762339/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree098.table
  base := (3497442108552358715721562308058457108061/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-15843668082758668708622329911401056128000000000000)
      constant := (422283146549399513696428028285278129447488880019525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree098.table
  base := (4371802634910485845455840712506850279159/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (9940438638)
      previous := (4970219319)
      next := (4970219319)
      square := (152637561803299406467080979734445800000000000000)
      linear := (-15847808861685257462562496759664292378000000000000)
      constant := (422498079553307436749005439847290333043905951216780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell157.Kernel098
