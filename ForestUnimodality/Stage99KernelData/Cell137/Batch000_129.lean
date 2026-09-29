import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell137.Parameters
import ForestUnimodality.BinomialMassData.Q23881_45156.Batch000_049
import ForestUnimodality.BinomialMassData.Q23881_45156.Batch050_099
import ForestUnimodality.BinomialMassData.Q23881_45156.Batch100_149
import ForestUnimodality.BinomialMassData.Q95549_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95549_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q95549_180624.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree000.table
  base := (5617321198820156940122672041/100000000000000000000000000)
  polynomial :=
    { denominator := 451560000000000000000000000000000000000000000
      center := (2889601)
      previous := (0)
      next := (2574275)
      square := (67051392397719473904560416399200000000000000)
      linear := (-310127517809946928841746684834800000000000000)
      constant := (25365575605392300678817937868339600000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree000.table
  base := (5617321198820156940122672041/100000000000000000000000000)
  polynomial :=
    { denominator := 1806240000000000000000000000000000000000000000
      center := (11561429)
      previous := (0)
      next := (10294075)
      square := (268205569590877895618241665596800000000000000)
      linear := (-1240510071239787715366986739339200000000000000)
      constant := (101462302421569202715271751473358400000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree001.table
  base := (21090101814703393009339674178879805822849/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-4301656699481460257851881977114704800000000000000)
      constant := (174079544670432572179001748312883723185906119253056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree001.table
  base := (337383172785720105789890987703534838953519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-17207464940330812524831334913663809200000000000000)
      constant := (696201364239318381754670198188991461181124154598384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (1247896610047016269/2500000000000000000)
  directionHi := (49915864401880650761/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree002.table
  base := (211836268744312993640578095928067070722719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-5102283850406429636009285629129352400000000000000)
      constant := (112536854974751543794066603970469715931671514462396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree002.table
  base := (105885500253901673617545744086372773136457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-20410811686435661530884756526927389600000000000000)
      constant := (450019983616611361337974737575167217757936660195104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1247896610047016269/2500000000000000000)
  centralHi := (49915864401880650761/100000000000000000000)
  directionLo := (2823667696588639859/4000000000000000000)
  directionHi := (17647923103678999119/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree003.table
  base := (139898847275191067147405264779256009587257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-1967637000443799671388896427048000000000000000000)
      constant := (26258558793103956207906711841382635830254152397196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree003.table
  base := (139843057104801429965726391529742507843573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-7871386144180170178979392713396990000000000000000)
      constant := (104999583496551592397423896277480414214843323704176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2823667696588639859/4000000000000000000)
  centralHi := (17647923103678999119/25000000000000000000)
  directionLo := (5403550827985997207/6250000000000000000)
  directionHi := (86456813247775955313/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree004.table
  base := (3042453040964728072831700411616004019569/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-6703538152256368392324092933158647600000000000000)
      constant := (60423543896634096792692112188132330985086351929472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree004.table
  base := (48657424031870526706534505995635158945749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-26817505178645359542991599753454550400000000000000)
      constant := (241620018179257082807661950048699211947936289415328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5403550827985997207/6250000000000000000)
  centralHi := (86456813247775955313/100000000000000000000)
  directionLo := (99831728803761301521/100000000000000000000)
  directionHi := (49915864401880650761/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree005.table
  base := (71096746674186580313169317600979296972603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-7504165303181337770481496585173295200000000000000)
      constant := (50793105336900798014666308780407628032796886596652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree005.table
  base := (1421268801100534555681961768821570841151/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-30020851924750208549045021366718130800000000000000)
      constant := (203125281349334381640743845992051314921926264536800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99831728803761301521/100000000000000000000)
  centralHi := (49915864401880650761/50000000000000000000)
  directionLo := (13951908244783377057/12500000000000000000)
  directionHi := (111615265958267016457/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree006.table
  base := (134993243565750871493001977178742892887/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-2768264151368769049546300079062647600000000000000)
      constant := (15418904455751328429850174466676684339978325934400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree006.table
  base := (431773292493002733819739219692423459571/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-11074732890285019185032814326660570400000000000000)
      constant := (61667389795436479934623512366224661492540164994000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13951908244783377057/12500000000000000000)
  centralHi := (111615265958267016457/100000000000000000000)
  directionLo := (61134198927281315649/50000000000000000000)
  directionHi := (122268397854562631299/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree007.table
  base := (42179093610422877089700315074127497811651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-9105419605031276526796303889202590400000000000000)
      constant := (44835937290816086735479184093814352126163899844684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree007.table
  base := (42158797004948078947741015711142774103441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-36427545416959906561151864593245291600000000000000)
      constant := (179337653555722196780562961923616170815930917980176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61134198927281315649/50000000000000000000)
  centralHi := (122268397854562631299/100000000000000000000)
  directionLo := (33016240921049514443/25000000000000000000)
  directionHi := (132064963684198057773/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree008.table
  base := (6701699767771672405904322403387071724851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-9906046755956245904953707541217238000000000000000)
      constant := (45443121641551506685900281276683240247022098767420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree008.table
  base := (33491821749242517549510691404099501964021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-39630892163064755567205286206508872000000000000000)
      constant := (181782359395000498558268662676414701850197176255056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33016240921049514443/25000000000000000000)
  centralHi := (132064963684198057773/100000000000000000000)
  directionLo := (141183384829431992951/100000000000000000000)
  directionHi := (17647923103678999119/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree009.table
  base := (26798423767773505760797219856185122866531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-3568891302293738427703703731077295200000000000000)
      constant := (15824376177765405148658626433845397370910120844868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree009.table
  base := (13392100432755749981640888181856851218029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-14278079636389868191086235939924150800000000000000)
      constant := (63305621949002649630552883507250768829794062742496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141183384829431992951/100000000000000000000)
  centralHi := (17647923103678999119/12500000000000000000)
  directionLo := (149747593205641952281/100000000000000000000)
  directionHi := (74873796602820976141/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree010.table
  base := (21376662831738805915164252406911068521417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-11507301057806184661268514845246533200000000000000)
      constant := (50583290367318209815316904186925531936418414221028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree010.table
  base := (21364144259577578396539444339045014459301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-46037585655274453579312129433036032800000000000000)
      constant := (202371349689429232731514015500099908032564992589136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149747593205641952281/100000000000000000000)
  centralHi := (74873796602820976141/50000000000000000000)
  directionLo := (15784782288606124379/10000000000000000000)
  directionHi := (157847822886061243791/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree011.table
  base := (526650976069948385063116825589413155417/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-12307928208731154039425918497261180800000000000000)
      constant := (54574602214644435383494971359845726605040239264896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree011.table
  base := (8420775307672031023454669721002691186339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-49240932401379302585365551046299613200000000000000)
      constant := (218350369241184925135093984399085544953670770611808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15784782288606124379/10000000000000000000)
  centralHi := (157847822886061243791/100000000000000000000)
  directionLo := (16555219330729597961/10000000000000000000)
  directionHi := (165552193307295979611/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree012.table
  base := (12992232632468697672488969889152321229997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-4369518453218707805861107383091942800000000000000)
      constant := (19775807946558287783785896825007838824308544673916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree012.table
  base := (3245476490395011931756422001602505959999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-17481426382494717197139657553187731200000000000000)
      constant := (79125245142414787130657427449647952801681871327552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16555219330729597961/10000000000000000000)
  centralHi := (165552193307295979611/100000000000000000000)
  directionLo := (276661802392883057/160000000000000000)
  directionHi := (86456813247775955313/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree013.table
  base := (9647367325870363369918592182048285395363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-13909182510581092795740725801290476000000000000000)
      constant := (64766564897664109588414257434336471594908588268492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree013.table
  base := (9637822933242575202328107673705160028557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-55647625893589000597472394272826774000000000000000)
      constant := (259146915927971428179990639043824273430903320243152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276661802392883057/160000000000000000)
  centralHi := (86456813247775955313/50000000000000000000)
  directionLo := (89987104280044159693/50000000000000000000)
  directionHi := (179974208560088319387/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree014.table
  base := (672055714053715533348384535726933731679/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-14709809661506062173898129453305123600000000000000)
      constant := (70842232368407744593802990872788096617255105750360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree014.table
  base := (6711690045933130278191644751926962286799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-58850972639693849603525815886090354400000000000000)
      constant := (283464874646745094793499548514791817225828844500464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89987104280044159693/50000000000000000000)
  centralHi := (179974208560088319387/100000000000000000000)
  directionLo := (93384031378251581233/50000000000000000000)
  directionHi := (186768062756503162467/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree015.table
  base := (4143401524144810565253242613919329097009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-5170145604143677184018511035106590400000000000000)
      constant := (25839852656734663906960752221195958178563178014252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree015.table
  base := (4135144956876748707435988623660101463827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-20684773128599566203193079166451311600000000000000)
      constant := (103396738789495841454132850273490917206177009924624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93384031378251581233/50000000000000000000)
  centralHi := (186768062756503162467/100000000000000000000)
  directionLo := (19332331154003140459/10000000000000000000)
  directionHi := (193323311540031404591/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree016.table
  base := (1865362796145555768802221139358537128737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-16311063963356000930212936757334418800000000000000)
      constant := (84772779307545569601413934220324427744084864355908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree016.table
  base := (464417764297670603628748840046775201007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-65257666131903547615632659112617515200000000000000)
      constant := (339219934477650244480168870153496343536730419945408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19332331154003140459/10000000000000000000)
  centralHi := (193323311540031404591/100000000000000000000)
  directionLo := (99831728803761301521/50000000000000000000)
  directionHi := (199663457607522603043/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree017.table
  base := (-152677392859292044913540658682270653833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-17111691114280970308370340409349066400000000000000)
      constant := (92581955172646967853315484822470025138567432000028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree017.table
  base := (-399597227297942451651556541998792613/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-68461012878008396621686080725881095600000000000000)
      constant := (370474286800367817438051707717288008668608580012800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99831728803761301521/50000000000000000000)
  centralHi := (199663457607522603043/100000000000000000000)
  directionLo := (10290419066148121599/5000000000000000000)
  directionHi := (205808381322962431981/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree018.table
  base := (-485534708051895021014553423712467419613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-5970772755068646562175914687121238000000000000000)
      constant := (33643689607512442384096908744586160588701728259344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree018.table
  base := (-243599891617486210212409008021551691039/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-23888119874704415209246500779714892000000000000000)
      constant := (134629739223008409941794754261375760056458358173056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10290419066148121599/5000000000000000000)
  centralHi := (205808381322962431981/100000000000000000000)
  directionLo := (211775077244147989427/100000000000000000000)
  directionHi := (52943769311036997357/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree019.table
  base := (-352895940182274211244706580720807706701/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-18712945416130909064685147713378361600000000000000)
      constant := (109806898005740816448726168468968859430380106711160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree019.table
  base := (-1767572482074032608471965956259322367253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-74867706370218094633792923952408256400000000000000)
      constant := (439411843347980317897924585840654672424314626821984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211775077244147989427/100000000000000000000)
  centralHi := (52943769311036997357/25000000000000000000)
  directionLo := (217578208607277083531/100000000000000000000)
  directionHi := (54394552151819270883/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree020.table
  base := (-493497024971358452825080907841148478591/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-19513572567055878442842551365393009200000000000000)
      constant := (119198313943427762107512182866234842460061080923560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree020.table
  base := (-4940706404628631433148884326406177392863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-78071053116322943639846345565671836800000000000000)
      constant := (476997651021823741592222746769818761628123595766032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217578208607277083531/100000000000000000000)
  centralHi := (54394552151819270883/25000000000000000000)
  directionLo := (223230531916534032913/100000000000000000000)
  directionHi := (111615265958267016457/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree021.table
  base := (-3089395754970398012825106662408933571109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-6771399905993615940333318339135885600000000000000)
      constant := (43031941574258163944891054936055443034559753021896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree021.table
  base := (-6184103082610841108361198361173313713619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-27091466620809264215299922392978472400000000000000)
      constant := (172202891356894550912211347777183335109706593202672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223230531916534032913/100000000000000000000)
  centralHi := (111615265958267016457/50000000000000000000)
  directionLo := (114371613500384849111/50000000000000000000)
  directionHi := (228743227000769698223/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree022.table
  base := (-7276447703743559486523765340967738960211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-21114826868905817199157358669422304400000000000000)
      constant := (139491261586340932545154083517664688539919006716276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree022.table
  base := (-7281359194365537580111557478787294337927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-84477746608532641651953188792198997600000000000000)
      constant := (558212238127431110484956448572845990735598322128528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114371613500384849111/50000000000000000000)
  centralHi := (228743227000769698223/100000000000000000000)
  directionLo := (117063078527895155777/50000000000000000000)
  directionHi := (46825231411158062311/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree023.table
  base := (-8241813491471922151193606924620138022209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-21915454019830786577314762321436952000000000000000)
      constant := (150377551702853610588040913871993576102879013040444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree023.table
  base := (-1649269808132294161515789798661611824759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-87681093354637490658006610405462578000000000000000)
      constant := (601780052600181619412126633621010663116790206524880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117063078527895155777/50000000000000000000)
  centralHi := (46825231411158062311/20000000000000000000)
  directionLo := (47877615202388486327/20000000000000000000)
  directionHi := (59847019002985607909/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree024.table
  base := (-9086952195643816712412734137987380084593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-7572027056918585318490721991150533200000000000000)
      constant := (53916181866544176798257795296417199737619145885396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree024.table
  base := (-142048991560399648248606745926758731877/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-30294813366914113221353344006242052800000000000000)
      constant := (215762506861810075472473860744476679504064489841664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47877615202388486327/20000000000000000000)
  centralHi := (59847019002985607909/25000000000000000000)
  directionLo := (61134198927281315649/25000000000000000000)
  directionHi := (244536795709125262597/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree025.table
  base := (-9822383056757841958180984605655584535227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-23516708321680725333629569625466247200000000000000)
      constant := (173598880924642067053705676150917629668746372158932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree025.table
  base := (-9826237060608639837460899818841669662933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-94087786846847188670113453631989738800000000000000)
      constant := (694713193963453561691691440804779021497120178542512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61134198927281315649/25000000000000000000)
  centralHi := (244536795709125262597/100000000000000000000)
  directionLo := (124789661004701626901/50000000000000000000)
  directionHi := (249579322009403253803/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree026.table
  base := (-2614324638294163681767957552651563310219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-24317335472605694711786973277480894800000000000000)
      constant := (185923871664185034256402365748920081019486332750416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree026.table
  base := (-10460845551695773443751915171736686156899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-97291133592952037676166875245253319200000000000000)
      constant := (744038330248640216866060858875309050824642348745936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124789661004701626901/50000000000000000000)
  centralHi := (249579322009403253803/100000000000000000000)
  directionLo := (6363049165576021983/2500000000000000000)
  directionHi := (254521966623040879321/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree027.table
  base := (-10999744927991648298604743963762452601031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-8372654207843554696648125643165180800000000000000)
      constant := (66239805372143273465552965174912337493778937589132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree027.table
  base := (-11003006293413984465187594477017459469081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-33498160113018962227406765619505633200000000000000)
      constant := (265082174811252895652905483691660796194923812734928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6363049165576021983/2500000000000000000)
  centralHi := (254521966623040879321/100000000000000000000)
  directionLo := (259370439743327865937/100000000000000000000)
  directionHi := (129685219871663932969/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree028.table
  base := (-11456774402045963939408580535844170397523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-25918589774455633468101780581510190000000000000000)
      constant := (211981919298373714172727074351470386422225976990068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree028.table
  base := (-5729885269665868513199529151405229848607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-103697827085161735688273718471780480000000000000000)
      constant := (848323398559133424038827440297616291263645574040096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259370439743327865937/100000000000000000000)
  centralHi := (129685219871663932969/50000000000000000000)
  directionLo := (33016240921049514443/12500000000000000000)
  directionHi := (52825985473679223109/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree029.table
  base := (-1479321853774743969951254796512147585121/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-26719216925380602846259184233524837600000000000000)
      constant := (225708226851477214074266646418838376186822489310688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree029.table
  base := (-2959331280139213502366139361229149730179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-106901173831266584694327140085044060400000000000000)
      constant := (903256337278099611096943331784229500483851912815424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33016240921049514443/12500000000000000000)
  centralHi := (52825985473679223109/20000000000000000000)
  directionLo := (10752206251788226803/4000000000000000000)
  directionHi := (67201289073676417519/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree030.table
  base := (-12138580916094931558734398483085035451687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-9173281358768524074805529295179828400000000000000)
      constant := (79965189449381441789992648055695479079597448938764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree030.table
  base := (-12141103685385530769674166394334263860791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-36701506859123811233460187232769213600000000000000)
      constant := (320011420344067369673201095235147950949549134383408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10752206251788226803/4000000000000000000)
  centralHi := (67201289073676417519/25000000000000000000)
  directionLo := (273400449102791488631/100000000000000000000)
  directionHi := (34175056137848936079/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree031.table
  base := (-386674064646993305936830376368730804623/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-28320471227230541602573991537554132800000000000000)
      constant := (254541508427314333906006464905643236895669254197376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree031.table
  base := (-6187941288379648451864386196784094755709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-113307867323476282706433983311571221200000000000000)
      constant := (1018647430550892339472886059625510559920678291411552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273400449102791488631/100000000000000000000)
  centralHi := (34175056137848936079/12500000000000000000)
  directionLo := (277919770956646794797/100000000000000000000)
  directionHi := (138959885478323397399/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree032.table
  base := (-1567968162896015003146266041509854492979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-29121098378155510980731395189568780400000000000000)
      constant := (269643904534416491172361087920506281821634317406112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree032.table
  base := (-6272931875025055302728245348762140516163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-116511214069581131712487404924834801600000000000000)
      constant := (1079087277776829878889273768414053441452942790274464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277919770956646794797/100000000000000000000)
  centralHi := (138959885478323397399/50000000000000000000)
  directionLo := (282366769658863985903/100000000000000000000)
  directionHi := (17647923103678999119/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree033.table
  base := (-12652807116097172296868732945876531476177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-9973908509693493452962932947194476000000000000000)
      constant := (95066956760595150206320002661152492883962170473044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree033.table
  base := (-12654746661601319593479211149511399655027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-39904853605228660239513608846032794000000000000000)
      constant := (380448753093507472654959184474220256758497247060976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282366769658863985903/100000000000000000000)
  centralHi := (17647923103678999119/6250000000000000000)
  directionLo := (143372405056350442069/50000000000000000000)
  directionHi := (286744810112700884139/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree034.table
  base := (-794000995056929587609065070750330679507/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-30722352680005449737046202493598075600000000000000)
      constant := (301210743621239913076033424931615003404842520950592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree034.table
  base := (-3176447678530112842990982970923763101511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-122917907561790829724594248151361962400000000000000)
      constant := (1205417728930152375527211397367777117889184688753216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143372405056350442069/50000000000000000000)
  centralHi := (286744810112700884139/100000000000000000000)
  directionLo := (291057004116987061397/100000000000000000000)
  directionHi := (145528502058493530699/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree035.table
  base := (-198441349478424154079888070117066268483/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-31522979830930419115203606145612723200000000000000)
      constant := (317672059154211215862747804765498903481803422043392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree035.table
  base := (-12701869582805118990726712927318486089827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-126121254307895678730647669764625542800000000000000)
      constant := (1271295827117111051054067180887815591338221671890128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291057004116987061397/100000000000000000000)
  centralHi := (145528502058493530699/50000000000000000000)
  directionLo := (144192498165970667/48828125000000000)
  directionHi := (295306236243907926017/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree036.table
  base := (-12644034656680293988463217362060166736107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-10774535660618462831120336599209123600000000000000)
      constant := (111527841336731397310644827303504044210182557735004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree036.table
  base := (-12645518539323816553914247225899108060041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-43108200351333509245567030459296374400000000000000)
      constant := (446325128086452382334284370895076284740186750067408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144192498165970667/48828125000000000)
  centralHi := (295306236243907926017/100000000000000000000)
  directionLo := (299495186411283904563/100000000000000000000)
  directionHi := (74873796602820976141/25000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree037.table
  base := (-626880990862402085495237033875000186187/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-33124234132780357871518413449642018400000000000000)
      constant := (351943996809594483855763991945742231041763642365840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree037.table
  base := (-6269487861693303498764396714108328509791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-132527947800105376742754512991152703600000000000000)
      constant := (1408451836646028888660451536733842591427726290172448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299495186411283904563/100000000000000000000)
  centralHi := (74873796602820976141/25000000000000000000)
  directionLo := (4744161713300099649/1562500000000000000)
  directionHi := (303626349651206377537/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree038.table
  base := (-2476595945212436652006522593780835474631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-33924861283705327249675817101656666000000000000000)
      constant := (369752469297422045956300959110623924529245368924980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree038.table
  base := (-6192109086763438462857331348616561423677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-135731294546210225748807934604416284000000000000000)
      constant := (1479721152968361949657051638343974325274053686633056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4744161713300099649/1562500000000000000)
  centralHi := (303626349651206377537/100000000000000000000)
  directionLo := (15385102674462686789/5000000000000000000)
  directionHi := (307702053489253735781/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree039.table
  base := (-12181862597808451392462055763925542300023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-11575162811543432209277740251223771200000000000000)
      constant := (129336016764374180319021471694737706561380307393356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree039.table
  base := (-6091496656613904767938387526263318168871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-46311547097438358251620452072559954800000000000000)
      constant := (517593256705817294079690199117589955830389545676896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15385102674462686789/5000000000000000000)
  centralHi := (307702053489253735781/100000000000000000000)
  directionLo := (62344894655614104451/20000000000000000000)
  directionHi := (19482779579879407641/6250000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree040.table
  base := (-5967907262183967469087498711857449003413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-35526115585555266005990624405685961200000000000000)
      constant := (406709951651492242011028564371077435710600904710616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree040.table
  base := (-11936846491068937203100707797914222097577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-142137988038419923760914777830943444800000000000000)
      constant := (1627624537028123473680914038132044886533647627286128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62344894655614104451/20000000000000000000)
  centralHi := (19482779579879407641/6250000000000000000)
  directionLo := (15784782288606124379/5000000000000000000)
  directionHi := (315695645772122487581/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree041.table
  base := (-5823101792828899525554303207394448352669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-36326742736480235384148028057700608800000000000000)
      constant := (425857475971789176793289599419992393689839345843608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree041.table
  base := (-2329429018160639340075093120454827993753/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-145341334784524772766968199444207025200000000000000)
      constant := (1704252665516932484773517153141352233632119134534960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15784782288606124379/5000000000000000000)
  centralHi := (315695645772122487581/100000000000000000000)
  directionLo := (319617481184093519607/100000000000000000000)
  directionHi := (39952185148011689951/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree042.table
  base := (-1414280122025961796958249360209495918249/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-12375789962468401587435143903238418800000000000000)
      constant := (148483335276040334357654023078542964789707261688224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree042.table
  base := (-11315099656678024134137998093867302968281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-49514893843543207257673873685823535200000000000000)
      constant := (594220562402092272864268552787025541116957091224528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319617481184093519607/100000000000000000000)
  centralHi := (39952185148011689951/12500000000000000000)
  directionLo := (161745886962738028553/50000000000000000000)
  directionHi := (323491773925476057107/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree043.table
  base := (-10940999532241997706828256868720512187661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-37927997038330174140462835361729904000000000000000)
      constant := (465486994324966846945927990652965769461621778910476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree043.table
  base := (-10941782418906652919302836693522078754139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-151748028276734470779075042670734186000000000000000)
      constant := (1862849415749768689207183842282855523621351852713296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161745886962738028553/50000000000000000000)
  centralHi := (323491773925476057107/100000000000000000000)
  directionLo := (327320212202727020959/100000000000000000000)
  directionHi := (2045751326267043881/625000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree044.table
  base := (-5263714996128175150396513956223547668883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-38728624189255143518620239013744551600000000000000)
      constant := (485967956808086877317946654274489652952492368871656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree044.table
  base := (-10528143552386643953818407097123796121343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-154951375022839319785128464283997766400000000000000)
      constant := (1944813913679661517736256934502863178552034360276752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327320212202727020959/100000000000000000000)
  centralHi := (2045751326267043881/625000000000000000)
  directionLo := (331104386614591959221/100000000000000000000)
  directionHi := (165552193307295979611/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree045.table
  base := (-5037187639792146889185192183705324897921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-13176417113393370965592547555253066400000000000000)
      constant := (168964154527918080817042231523066027027892741392424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree045.table
  base := (-2518756364311860402641342986021263968807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-52718240589648056263727295299087115600000000000000)
      constant := (676184487762631570791929363416341908617251773110464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331104386614591959221/100000000000000000000)
  centralHi := (165552193307295979611/50000000000000000000)
  directionLo := (33484579787480104937/10000000000000000000)
  directionHi := (334845797874801049371/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree046.table
  base := (-4791291528581697446487298531681882896157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-40329878491105082274935046317773846800000000000000)
      constant := (528260133518761107005091525066492645244558934921624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree046.table
  base := (-9583175311503905482485527928463329496049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-161358068515049017797235307510524927200000000000000)
      constant := (2114066541030425529651762214558727872290789631191536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33484579787480104937/10000000000000000000)
  centralHi := (334845797874801049371/100000000000000000000)
  directionLo := (84636465941622591671/25000000000000000000)
  directionHi := (67709172753298073337/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree047.table
  base := (-9052716771722393074763793261503060621633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-41130505642030051653092449969788494400000000000000)
      constant := (550070628410466618870273045731659500682895539904828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree047.table
  base := (-9053256113089928764716373093511617385793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-164561415261153866803288729123788507600000000000000)
      constant := (2201351795011812126264341346555702639324451940621552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84636465941622591671/25000000000000000000)
  centralHi := (67709172753298073337/20000000000000000000)
  directionLo := (342205925419747796197/100000000000000000000)
  directionHi := (171102962709873898099/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree048.table
  base := (-4242682688077894444359274586069189818161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-13977044264318340343749951207267714000000000000000)
      constant := (190774549343553362676175106897968479035562263298984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree048.table
  base := (-1697171280015803339315787160299105925227/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-55921587335752905269780716912350696000000000000000)
      constant := (763469341721686146511172277483869911091972235992880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342205925419747796197/100000000000000000000)
  centralHi := (171102962709873898099/50000000000000000000)
  directionLo := (276661802392883057/80000000000000000)
  directionHi := (345827252991103821251/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree049.table
  base := (-7881051894280974832964860968957644112873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-42731759943879990409407257273817789600000000000000)
      constant := (595018925759538283574987683545170579048715076800668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree049.table
  base := (-315259952532704576621852031606616278377/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-170968108753363564815395572350315668400000000000000)
      constant := (2381234165791853946327086687997796521465610283433200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276661802392883057/80000000000000000)
  centralHi := (345827252991103821251/100000000000000000000)
  directionLo := (349411050813164555323/100000000000000000000)
  directionHi := (87352762703291138831/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree050.table
  base := (-905030121366734057286889959504157338087/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-43532387094804959787564660925832437200000000000000)
      constant := (618156224736922746958181490016116787056348207669536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree050.table
  base := (-7240647644449998183104207769628253905453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-174171455499468413821448993963579248800000000000000)
      constant := (2473829270171665300121723930978804832233438071775792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349411050813164555323/100000000000000000000)
  centralHi := (87352762703291138831/25000000000000000000)
  directionLo := (352958462073579982379/100000000000000000000)
  directionHi := (17647923103678999119/5000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree051.table
  base := (-1312669106396425256675787079160897768481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-14777671415243309721907354859282361600000000000000)
      constant := (213911778155736982243173489358338919314395170002660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree051.table
  base := (-328185774696518410495040917081297695011/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-59124934081857754275834138525614276400000000000000)
      constant := (856064165661873774622164069209519385195860431815360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352958462073579982379/100000000000000000000)
  centralHi := (17647923103678999119/5000000000000000000)
  directionLo := (71294114614976104579/20000000000000000000)
  directionHi := (22279410817180032681/6250000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree052.table
  base := (-5850732662919143586631722215048299697717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-45133641396654898543879468229861732400000000000000)
      constant := (665756067822668415452869694357615761992236421169772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree052.table
  base := (-1462767286924260226451455460820651293061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-180578148991678111833555837190106409600000000000000)
      constant := (2664323098333596250274142676012327262024108122510016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71294114614976104579/20000000000000000000)
  centralHi := (22279410817180032681/6250000000000000000)
  directionLo := (359948417120176638773/100000000000000000000)
  directionHi := (179974208560088319387/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree053.table
  base := (-1020545760180980283921587268764011750159/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96182280000000000000000000000000000000000000000
      center := (615485013)
      previous := (0)
      next := (548320575)
      square := (14281946580714247941671368693029600000000000000)
      linear := (-866684312218488074000695695884460000000000000000)
      constant := (13022986007484951689530724294508762133961458508740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree053.table
  base := (-20412139069529336221792812749584597013/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2462584377)
      previous := (0)
      next := (2192637975)
      square := (57127786322856991766685474772118400000000000000)
      linear := (-3467575391278923789426589788742830000000000000000)
      constant := (52117366210396940539717355547217807528140847036000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359948417120176638773/100000000000000000000)
  centralHi := (179974208560088319387/50000000000000000000)
  directionLo := (363392978064116707781/100000000000000000000)
  directionHi := (181696489032058353891/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree054.table
  base := (-539953040393400236190419883574151710723/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-15578298566168279100064758511297009200000000000000)
      constant := (238373919388286971623951403619885533223474227950048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree054.table
  base := (-4319902476956406373769537952572834078891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-62328280827962603281887560138877856800000000000000)
      constant := (953961279285501849831742251504407733912429317156208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363392978064116707781/100000000000000000000)
  centralHi := (181696489032058353891/50000000000000000000)
  directionLo := (73361038712737578779/20000000000000000000)
  directionHi := (45850649195460986737/12500000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree055.table
  base := (-700335520823752541082243044847845719457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-47535522849429806678351679185905675200000000000000)
      constant := (740466435416600678561675845659728408808781212518060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree055.table
  base := (-3501930418302610219436871321002918422673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-190188189229992658851716102029897150800000000000000)
      constant := (2963312858082091381278083955214860691229910111909872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73361038712737578779/20000000000000000000)
  centralHi := (45850649195460986737/12500000000000000000)
  directionLo := (370185958059299540901/100000000000000000000)
  directionHi := (185092979029649770451/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree056.table
  base := (-662279651266459904876622841038672900579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-48336150000354776056509082837920322800000000000000)
      constant := (766252172925477755060113988666062184891659687349456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree056.table
  base := (-2649348339180368279340166580920192996651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-193391535976097507857769523643160731200000000000000)
      constant := (3066507001357332829244804827210069456398291978461264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370185958059299540901/100000000000000000000)
  centralHi := (185092979029649770451/50000000000000000000)
  directionLo := (93384031378251581233/25000000000000000000)
  directionHi := (373536125513006324933/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree057.table
  base := (-1762152051398203748336939697869451255737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-16378925717093248478222162163311656800000000000000)
      constant := (264159622109807236683253326652494516513378022325364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree057.table
  base := (-220295096145537133823459768846517506731/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-65531627574067452287940981752141437200000000000000)
      constant := (1057155283544422878534825798354326271897100474545024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93384031378251581233/25000000000000000000)
  centralHi := (373536125513006324933/100000000000000000000)
  directionLo := (188428255963811960523/50000000000000000000)
  directionHi := (376856511927623921047/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree058.table
  base := (-52560015418720667668312545434878014237/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-49937404302204714812823890141949618000000000000000)
      constant := (819146422696248594058370190214869853322635332193472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree058.table
  base := (-841149832296475248323493273231814127893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-199798229468307205869876366869687892000000000000000)
      constant := (3278189034547259869608090507535781566301232440875952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188428255963811960523/50000000000000000000)
  centralHi := (376856511927623921047/100000000000000000000)
  directionLo := (95036974416948075081/25000000000000000000)
  directionHi := (15205915906711692013/4000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree059.table
  base := (114294433874832670968954410462992720721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-50738031453129684190981293793964265600000000000000)
      constant := (846254759252611327001778840806292812276162449826564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree059.table
  base := (22824452156822174183735552430879777299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-203001576214412054875929788482951472400000000000000)
      constant := (3386676222341377654486408268835307439132470066542320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95036974416948075081/25000000000000000000)
  centralHi := (15205915906711692013/4000000000000000000)
  directionLo := (383411029601691587311/100000000000000000000)
  directionHi := (23963189350105724207/6250000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree060.table
  base := (1103467333256559948550924897666360144313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-17179552868018217856379565815326304400000000000000)
      constant := (291267934085747555076308578554393514383100037626764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree060.table
  base := (110331100368226294329202114762882258803/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-68734974320172301293994403365405017600000000000000)
      constant := (1165642373119261739124948791959641798701641064499360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383411029601691587311/100000000000000000000)
  centralHi := (23963189350105724207/6250000000000000000)
  directionLo := (386646623080062809181/100000000000000000000)
  directionHi := (193323311540031404591/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree061.table
  base := (2126429552173935345544660027854385723287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-52339285754979622947296101097993560800000000000000)
      constant := (901793486001665635722185794277038566382385521598108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree061.table
  base := (531571908763924504572206909374969465329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-209408269706621752888036631709478633200000000000000)
      constant := (3608941463043821653620203705650688276588865409626176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386646623080062809181/100000000000000000000)
  centralHi := (193323311540031404591/50000000000000000000)
  directionLo := (97463840941847214947/25000000000000000000)
  directionHi := (389855363767388859789/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree062.table
  base := (3183066209884317520328224975114507054877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-53139912905904592325453504750008208400000000000000)
      constant := (930223751923573935193023896723158213312955021391668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree062.table
  base := (795734350092165692911833323321476910639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-212611616452726601894090053322742213600000000000000)
      constant := (3722719019407605714382084651775187235675325775482816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97463840941847214947/25000000000000000000)
  centralHi := (389855363767388859789/100000000000000000000)
  directionLo := (393037909338514101753/100000000000000000000)
  directionHi := (196518954669257050877/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree063.table
  base := (213663745019054661380779293925844126649/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-17980180018943187234536969467340952000000000000000)
      constant := (319698182606619531443096016686787292662241738483440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree063.table
  base := (2136579004522923760116623409152339361657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-71938321066277150300047824978668598000000000000000)
      constant := (1279419859957357792254484873390240778834715863043168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393037909338514101753/100000000000000000000)
  centralHi := (196518954669257050877/50000000000000000000)
  directionLo := (396194891052594173317/100000000000000000000)
  directionHi := (198097445526297086659/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree064.table
  base := (674620540196673791080006090904214665633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-54741167207754531081768312054037503600000000000000)
      constant := (988405827147810288228654452093123621833560830329376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree064.table
  base := (5396858264529099169720428465159578464711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-219018309944936299906196896549269374400000000000000)
      constant := (3955562958481575344839645135325825097396185834646896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396194891052594173317/100000000000000000000)
  centralHi := (198097445526297086659/50000000000000000000)
  directionLo := (99831728803761301521/25000000000000000000)
  directionHi := (79865383043009041217/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree065.table
  base := (6554053057606588316827956784725442970077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-55541794358679500459925715706052151200000000000000)
      constant := (1018157548404387631482180953569297449328021481468468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree065.table
  base := (6553956847409167684753323617630818287169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-222221656691041148912250318162532954800000000000000)
      constant := (4074628989420604392275055946743061580321362914304784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99831728803761301521/25000000000000000000)
  centralHi := (79865383043009041217/20000000000000000000)
  directionLo := (40243456453708202633/10000000000000000000)
  directionHi := (402434564537082026331/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree066.table
  base := (7744468496833079975960006038295254378467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-18780807169868156612694373119355599600000000000000)
      constant := (349449891524878456857095099532375141286764992171076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree066.table
  base := (1548876246829210748664417909501489577089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-75141667812381999306101246591932178400000000000000)
      constant := (1398485841602998861994237534758122631809196504329840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40243456453708202633/10000000000000000000)
  centralHi := (402434564537082026331/100000000000000000000)
  directionLo := (10137959985036985193/2500000000000000000)
  directionHi := (405518399401479407721/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree067.table
  base := (8968145869997823821269138621649648488783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-57143048660529439216240523010081446400000000000000)
      constant := (1078982172641383999401020238435905710780103427835772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree067.table
  base := (8968066735946492389103933336604728259257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-228628350183250846924357161389060115600000000000000)
      constant := (4318048432742140640513178703176360175559922310558352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10137959985036985193/2500000000000000000)
  centralHi := (405518399401479407721/100000000000000000000)
  directionLo := (408578959042343136711/100000000000000000000)
  directionHi := (51072369880292892089/12500000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree068.table
  base := (5112513697504202543168539690116280489369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-57943675811454408594397926662096094000000000000000)
      constant := (1110055013149282542369804954254065770419422477521992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree068.table
  base := (10224955644172140528119371646172561737439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-231831696929355695930410583002323696000000000000000)
      constant := (4442401595548410231341388782657286889740570060875504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408578959042343136711/100000000000000000000)
  centralHi := (51072369880292892089/12500000000000000000)
  directionLo := (411616762645924863961/100000000000000000000)
  directionHi := (205808381322962431981/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree069.table
  base := (5757530758123094415230328976600238822921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-19581434320793125990851776771370247200000000000000)
      constant := (380522723272341726582163872896791179202150138407576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree069.table
  base := (179921819847480293996344892278246955137/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-78345014558486848312154668205195758800000000000000)
      constant := (1522838969413089828035596498239101660915336238806016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411616762645924863961/100000000000000000000)
  centralHi := (205808381322962431981/50000000000000000000)
  directionLo := (12957259699338895973/3125000000000000000)
  directionHi := (414632310378844671137/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree070.table
  base := (12838202227771136880610924775587030148421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-59544930113304347350712733966125389200000000000000)
      constant := (1173521619192344017532804749706462603159950511953364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree070.table
  base := (12838143269362331930416258072524574258353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-238238390421565393942517426228850856800000000000000)
      constant := (4696394277130348010288032224419535125603791252398608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12957259699338895973/3125000000000000000)
  centralHi := (414632310378844671137/100000000000000000000)
  directionLo := (208813042174743911737/50000000000000000000)
  directionHi := (16705043373979512939/4000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree071.table
  base := (7097204235500907248242548521161425967059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71798040000000000000000000000000000000000000000
      center := (459446559)
      previous := (0)
      next := (409309725)
      square := (10661171391237396350825106207472800000000000000)
      linear := (-849937426256750939843241374903380800000000000000)
      constant := (16984723103450236382339135785035073531607988152872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree071.table
  base := (7097177519368702103683124634566183049109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 287192160000000000000000000000000000000000000000
      center := (1838267211)
      previous := (0)
      next := (1636757925)
      square := (42644685564949585403300424829891200000000000000)
      linear := (-3400587847431975252796772504818513200000000000000)
      constant := (67972304487525174745762399569295839117065799957088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208813042174743911737/50000000000000000000)
  centralHi := (16705043373979512939/4000000000000000000)
  directionLo := (420598549507808519671/100000000000000000000)
  directionHi := (52574818688476064959/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree072.table
  base := (3116728719706954959211421742413363965369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-20382061471718095369009180423384894800000000000000)
      constant := (412916438197763377567053618037212181296488111241660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree072.table
  base := (15583595181814266001630131229688717035673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-81548361304591697318208089818459339200000000000000)
      constant := (1652478286022789460427708216089933079229678818019376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420598549507808519671/100000000000000000000)
  centralHi := (52574818688476064959/12500000000000000000)
  directionLo := (84710030897659195771/20000000000000000000)
  directionHi := (52943769311036997357/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree073.table
  base := (8502937448360969670552812107746505023201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-61946811566079255485184944922169332000000000000000)
      constant := (1272023525261005791898474463670476385910727005829768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree073.table
  base := (3401166206259454648998108169940645599811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-247848430659879940960677691068641598000000000000000)
      constant := (5090597928881873431902363084766590492534449692202480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84710030897659195771/20000000000000000000)
  centralHi := (52943769311036997357/12500000000000000000)
  directionLo := (426481332400430307859/100000000000000000000)
  directionHi := (21324066620021515393/5000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree074.table
  base := (1846107316046653143555870642813239429573/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-62747438717004224863342348574183979600000000000000)
      constant := (1305737957460345944040640419843774949673678220021320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree074.table
  base := (18461033424327220358940422503603503103741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-251051777405984789966731112681905178400000000000000)
      constant := (5225522771589856416922419693659905499813503581280976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426481332400430307859/100000000000000000000)
  centralHi := (21324066620021515393/5000000000000000000)
  directionLo := (429392501570571516513/100000000000000000000)
  directionHi := (214696250785285758257/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree075.table
  base := (9974606157220647062564143128885102279427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-21182688622643064747166584075399542400000000000000)
      constant := (446630865966331041443869842214157492666615317035912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree075.table
  base := (249364704050678077578939594164553392519/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-84751708050696546324261511431722919600000000000000)
      constant := (1787403111033835120903983239091120098827254722730240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429392501570571516513/100000000000000000000)
  centralHi := (214696250785285758257/50000000000000000000)
  directionLo := (216142033119439888281/50000000000000000000)
  directionHi := (432284066238879776563/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree076.table
  base := (21470269075589124401116024306167166895687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-64348693018854163619657155878213274800000000000000)
      constant := (1374487434708034489822253013654225619717788798479708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree076.table
  base := (5367559120615955543456266068718407611211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-257458470898194487978837955908432339200000000000000)
      constant := (5500657566012622961165742568918164529746925215483584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216142033119439888281/50000000000000000000)
  centralHi := (432284066238879776563/100000000000000000000)
  directionLo := (217578208607277083531/50000000000000000000)
  directionHi := (435156417214554167063/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree077.table
  base := (23024222652346353224830193608600561745603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-65149320169779132997814559530227922400000000000000)
      constant := (1409522457288636048710044954741030467931256245528652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree077.table
  base := (23024193139898326189278777799774156768611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-260661817644299336984891377521695919600000000000000)
      constant := (5640867427992931727545826480172450023758847694357296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217578208607277083531/50000000000000000000)
  centralHi := (435156417214554167063/100000000000000000000)
  directionLo := (109502483123099219461/25000000000000000000)
  directionHi := (87601986498479375569/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree078.table
  base := (24611054476541858679963330644631712089777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-21983315773568034125323987727414190000000000000000)
      constant := (481665885391791307044607572828033381431407025907756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree078.table
  base := (24611027757229508066349058817352838562877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-87955054796801395330314933044986500000000000000000)
      constant := (1927612960413318808789058734060983464330642661418224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109502483123099219461/25000000000000000000)
  centralHi := (87601986498479375569/20000000000000000000)
  directionLo := (55105622229182098417/12500000000000000000)
  directionHi := (440844977833456787337/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree079.table
  base := (5246149592875807165132843701687062627173/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-66750574471629071754129366834257217600000000000000)
      constant := (1480913022914391053940393528414717486394583661002660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree079.table
  base := (6557680944272709849086815985746994422361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-267068511136509034996998220748223080400000000000000)
      constant := (5926571891992161471471503889695861201920808944069184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55105622229182098417/12500000000000000000)
  centralHi := (440844977833456787337/100000000000000000000)
  directionLo := (221830953656138767319/50000000000000000000)
  directionHi := (443661907312277534639/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree080.table
  base := (27883288303309386917427046392479999919067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-67551201622554041132286770486271865200000000000000)
      constant := (1517268549954752605374457824842282352607063101523628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree080.table
  base := (13941633205490170352217098037700048394873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-270271857882613884003051642361486660800000000000000)
      constant := (6072066430094839893646260926567088888294919159098656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221830953656138767319/50000000000000000000)
  centralHi := (443661907312277534639/100000000000000000000)
  directionLo := (446461063833068065827/100000000000000000000)
  directionHi := (111615265958267016457/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree081.table
  base := (29568662261962299302282217328622297822549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-22783942924493003503481391379428837600000000000000)
      constant := (518021410183851530757076815116428657042027510209372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree081.table
  base := (29568642449400149509349773889484282094217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-91158401542906244336368354658250080400000000000000)
      constant := (2073107489537658568345892470875384133662793758848304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446461063833068065827/100000000000000000000)
  centralHi := (111615265958267016457/25000000000000000000)
  directionLo := (112310694904231464211/25000000000000000000)
  directionHi := (89848555923385171369/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree082.table
  base := (7821714505152712659027039468602263108613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-69152455924403979888601577790301160400000000000000)
      constant := (1591300058679501107477976435022050598073661262725968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree082.table
  base := (31286840092514240354561816469587559301091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-276678551374823582015158485588013821600000000000000)
      constant := (6368339983485944095489350459531643935950139743990576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112310694904231464211/25000000000000000000)
  centralHi := (89848555923385171369/20000000000000000000)
  directionLo := (90401475332414514769/20000000000000000000)
  directionHi := (226003688331036286923/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree083.table
  base := (16518932509966484435294596449522406198443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-69953083075328949266758981442315808000000000000000)
      constant := (1628976028955807888631860053353334448406075230014424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree083.table
  base := (33037848799085078414233350888832574218841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-279881898120928431021211907201277402000000000000000)
      constant := (6519118953219483550433357924438170344402211742354576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90401475332414514769/20000000000000000000)
  centralHi := (226003688331036286923/50000000000000000000)
  directionLo := (454755167178907034863/100000000000000000000)
  directionHi := (28422197948681689679/6250000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree084.table
  base := (8705418456518787366277184605014144275011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-23584570075417972881638795031443485200000000000000)
      constant := (555697378857138792564511655126978378655577835369232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree084.table
  base := (17410829575848876725204979482366563621811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-94361748289011093342421776271513660800000000000000)
      constant := (2223886452870293063029615226545398025640073201221664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454755167178907034863/100000000000000000000)
  centralHi := (28422197948681689679/6250000000000000000)
  directionLo := (91497290800307879289/20000000000000000000)
  directionHi := (228743227000769698223/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree085.table
  base := (4579784501280732953588824642689798868597/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-71554337377178888023073788746345103200000000000000)
      constant := (1705648377229614524178862175793777097217938586113184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree085.table
  base := (36638262736499969578624011231219199394317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-286288591613138129033318750427804562800000000000000)
      constant := (6825961182503744866546076205534989035720924595778512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91497290800307879289/20000000000000000000)
  centralHi := (228743227000769698223/50000000000000000000)
  directionLo := (230100765488671048673/50000000000000000000)
  directionHi := (460201530977342097347/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree086.table
  base := (4810958005157626063216720861388492905593/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-72354964528103857401231192398359750800000000000000)
      constant := (1744644747091260100092058158282960094649167402462496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree086.table
  base := (19243826017940693804665833994528960816229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-289491938359242978039372172041068143200000000000000)
      constant := (6982024409569189448218787514495348510989028007817888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230100765488671048673/50000000000000000000)
  centralHi := (460201530977342097347/100000000000000000000)
  directionLo := (462900683335935996969/100000000000000000000)
  directionHi := (46290068333593599697/10000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree087.table
  base := (20184915594818548742805935448333589327037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-24385197226342942259796198683458132800000000000000)
      constant := (594693747575296887040329352646424185387938564542072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree087.table
  base := (40369820332689074756791925743906423646919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-97565095035115942348475197884777241200000000000000)
      constant := (2379949675370168649801923332319702192705746529726928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462900683335935996969/100000000000000000000)
  centralHi := (46290068333593599697/10000000000000000000)
  directionLo := (11639604700973080887/2500000000000000000)
  directionHi := (465584188038923235481/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree088.table
  base := (5285596430247734155123980813871066649237/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-73956218829953796157545999702389046000000000000000)
      constant := (1823957861068082784691966797931630613013476376623264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree088.table
  base := (42284761624729717916581492860957239016053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-295898631851452676051479015267595304000000000000000)
      constant := (7299435019888836047578112675106000196098661403785808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11639604700973080887/2500000000000000000)
  centralHi := (465584188038923235481/100000000000000000000)
  directionLo := (468252314111580623109/100000000000000000000)
  directionHi := (46825231411158062311/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree089.table
  base := (11058119856142214690329576567911574574839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-74756845980878765535703403354403693600000000000000)
      constant := (1864274599378492968132207531728241400567158567841904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree089.table
  base := (22116235274223006129277831911821734983783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-299101978597557525057532436880858884400000000000000)
      constant := (7460782379967541328364386942197975346527650907326176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468252314111580623109/100000000000000000000)
  centralHi := (46825231411158062311/10000000000000000000)
  directionLo := (470905322957637952761/100000000000000000000)
  directionHi := (235452661478818976381/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree090.table
  base := (46212950335103993895776340926751651757619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-25185824377267911637953602335472780400000000000000)
      constant := (635010485069691524727389631210307866119004384931332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree090.table
  base := (23106471155388098788262667873711543309769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-100768441781220791354528619498040821600000000000000)
      constant := (2541297032191086832094256197357109216859646245532256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470905322957637952761/100000000000000000000)
  centralHi := (235452661478818976381/50000000000000000000)
  directionLo := (473543468658183731371/100000000000000000000)
  directionHi := (118385867164545932843/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree091.table
  base := (3014136242612541245840138637337562089059/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-76358100282728704292018210658432988800000000000000)
      constant := (1946228426372020344857982164613206317645943450799296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree091.table
  base := (48226172628313803535405574508571433545063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-305508672089767223069639280107386045200000000000000)
      constant := (7788761160971852181081343966023460751887632012173168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473543468658183731371/100000000000000000000)
  centralHi := (118385867164545932843/25000000000000000000)
  directionLo := (476166998255665733699/100000000000000000000)
  directionHi := (4761669982556657337/1000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree092.table
  base := (10054432845795119027632401961972367271047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-77158727433653673670175614310447636400000000000000)
      constant := (1987865510912029044360061115437772068499856978849740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree092.table
  base := (628401970912260049371735516343129929029/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-308712018835872072075692701720649625600000000000000)
      constant := (7955392565357619004140072474845696317551779600779520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476166998255665733699/100000000000000000000)
  centralHi := (4761669982556657337/1000000000000000000)
  directionLo := (47877615202388486327/10000000000000000000)
  directionHi := (478776152023884863271/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree093.table
  base := (52350899948463796074958531301716920977973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-25986451528192881016111005987487428000000000000000)
      constant := (676647569027179474527170292717289586444492915489244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree093.table
  base := (10470178804702583071604298339489756683521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-103971788527325640360582041111304402000000000000000)
      constant := (2707928434251460993674002469404308341030308850011760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47877615202388486327/10000000000000000000)
  centralHi := (478776152023884863271/100000000000000000000)
  directionLo := (481371163724817490061/100000000000000000000)
  directionHi := (240685581862408745031/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree094.table
  base := (13615595994056668455276898711011782268449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-78759981735503612426490421614476931600000000000000)
      constant := (2072460013318605529822308564913867829299391533934864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree094.table
  base := (27231189311065948466882711274316599422923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-315118712328081770087799544947176786400000000000000)
      constant := (8293939366927137553461037710904609694462160940348256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481371163724817490061/100000000000000000000)
  centralHi := (240685581862408745031/50000000000000000000)
  directionLo := (241976130426521606223/50000000000000000000)
  directionHi := (483952260853043212447/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree095.table
  base := (56606613573595544697144631354189607377027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-79560608886428581804647825266491579200000000000000)
      constant := (2115417428227149952829738811125752763396084565352268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree095.table
  base := (566066087358474708590423917700866881907/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-318322059074186619093852966560440366800000000000000)
      constant := (8465854752303139715323894003065987504455508736875200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241976130426521606223/50000000000000000000)
  centralHi := (483952260853043212447/100000000000000000000)
  directionLo := (19460786594740056099/4000000000000000000)
  directionHi := (121629916217125350619/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree096.table
  base := (459246767911350900600883172328832363687/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-26787078679117850394268409639502075600000000000000)
      constant := (719604983519768792674951342099593094798045260446208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree096.table
  base := (29391790960945908851074682733856035651637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-107175135273430489366635462724567982400000000000000)
      constant := (2879843817967142908292967613513535230703731684478688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19460786594740056099/4000000000000000000)
  centralHi := (121629916217125350619/25000000000000000000)
  directionLo := (489073591418250525193/100000000000000000000)
  directionHi := (244536795709125262597/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree097.table
  base := (30496649972653899000925571471393332708649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-81161863188278520560962632570520874400000000000000)
      constant := (2202652579199660231244233493984020693327194227321032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree097.table
  base := (60993295996843336688921486412812830994029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-324728752566396317105959809786967527600000000000000)
      constant := (8814969467269867465535434672768897393460619962849744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489073591418250525193/100000000000000000000)
  centralHi := (244536795709125262597/50000000000000000000)
  directionLo := (245807125273929350827/50000000000000000000)
  directionHi := (98322850109571740331/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree098.table
  base := (63235752575669199640670912089652818542021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-81962490339203489939120036222535522000000000000000)
      constant := (2246930313151164620137493019089106285027728634615764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree098.table
  base := (63235749009044228698918509595315355792339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-327932099312501166112013231400231108000000000000000)
      constant := (8992168788428900123030747627531719546619309476921904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245807125273929350827/50000000000000000000)
  centralHi := (98322850109571740331/20000000000000000000)
  directionLo := (494141846903011975331/100000000000000000000)
  directionHi := (123535461725752993833/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree099.table
  base := (65510942435364610024137195925959366372673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-27587705830042819772425813291516723200000000000000)
      constant := (763882717174186178940803806021020909329639599940844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree099.table
  base := (65510939213959110043843675531219570505037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-110378482019535338372688884337831562800000000000000)
      constant := (3057043137940435604531986547326959278546519485020144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494141846903011975331/100000000000000000000)
  centralHi := (123535461725752993833/25000000000000000000)
  directionLo := (496656579921887938831/100000000000000000000)
  directionHi := (31041036245117996177/6250000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree100.table
  base := (67818867961488359528007367641183327863173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-83563744641053428695434843526564817200000000000000)
      constant := (2336806093517125678433240775570816312170897788024532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree100.table
  base := (33909432526079936979867283896669262800567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-334338792804710864124120074626758268800000000000000)
      constant := (9351851340267313300172674582735314810928095300557024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496656579921887938831/100000000000000000000)
  centralHi := (31041036245117996177/6250000000000000000)
  directionLo := (99831728803761301521/20000000000000000000)
  directionHi := (249579322009403253803/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree101.table
  base := (70159527756898622403737738221493926455007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-84364371791978398073592247178579464800000000000000)
      constant := (2382404138422650527665535606560872700768752920582588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree101.table
  base := (35079762564827947894857596410432499902637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-337542139550815713130173496240021849200000000000000)
      constant := (9534334564924483015304694374150622820211081158108064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99831728803761301521/20000000000000000000)
  centralHi := (249579322009403253803/50000000000000000000)
  directionLo := (100329645751927288193/20000000000000000000)
  directionHi := (250824114379818220483/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree102.table
  base := (9066615071576509201781739794562076715671/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-28388332980967789150583216943531370800000000000000)
      constant := (809480761867481248644615781592593534779347165606304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree102.table
  base := (72532918200318881205798616680947795539951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-113581828765640187378742305951095143200000000000000)
      constant := (3239526361750626731982436590856778922571111315762512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100329645751927288193/20000000000000000000)
  centralHi := (250824114379818220483/50000000000000000000)
  directionLo := (100825103805881096573/20000000000000000000)
  directionHi := (252062759514702741433/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree103.table
  base := (9367380661509020359242736736244103847089/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-85965626093828336829907054482608760000000000000000)
      constant := (2474920534487322673034529452689593728539759154635808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree103.table
  base := (2997561726007143515567117594961214206209/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-343948833043025411142280339466549010000000000000000)
      constant := (9904584898978047849622963687154174628915933041555600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100825103805881096573/20000000000000000000)
  centralHi := (252062759514702741433/50000000000000000000)
  directionLo := (126647673798133380283/25000000000000000000)
  directionHi := (506590695192533521133/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree104.table
  base := (15475580183418201936637091401489155943603/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-86766253244753306208064458134623407600000000000000)
      constant := (2521838884568444982029032612535826623569179130803260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree104.table
  base := (77377898983389668255391123867169391468731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-347152179789130260148333761079812590400000000000000)
      constant := (10092352004072393243900655827383753985814712041277616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126647673798133380283/25000000000000000000)
  centralHi := (506590695192533521133/100000000000000000000)
  directionLo := (6363049165576021983/1250000000000000000)
  directionHi := (509043933246081758641/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree105.table
  base := (79849486555286365989416803594135307751287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-29188960131892758528740620595546018400000000000000)
      constant := (856399111796968156298827569556126046149502806650036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree105.table
  base := (19962371202422825654441162894884736602581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-116785175511745036384795727564358723600000000000000)
      constant := (3427293466239872430539721176701291932628602296868288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6363049165576021983/1250000000000000000)
  centralHi := (509043933246081758641/100000000000000000000)
  directionLo := (255742702483193192263/50000000000000000000)
  directionHi := (511485404966386384527/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree106.table
  base := (82353801408854222059902391889485811764283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96182280000000000000000000000000000000000000000
      center := (615485013)
      previous := (0)
      next := (548320575)
      square := (14281946580714247941671368693029600000000000000)
      linear := (-1667311463143457452158099347899107600000000000000)
      constant := (49377280878264296373508042960160935340313956150524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree106.table
  base := (41176899916600200922215186454595793266167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2462584377)
      previous := (0)
      next := (2192637975)
      square := (57127786322856991766685474772118400000000000000)
      linear := (-6670922137383772795480011402006410400000000000000)
      constant := (197606982665978550379324249988440835649798871136608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255742702483193192263/50000000000000000000)
  centralHi := (511485404966386384527/100000000000000000000)
  directionLo := (513915278049422474581/100000000000000000000)
  directionHi := (256957639024711237291/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree107.table
  base := (21222711191133674558535599575062454376203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-89168134697528214342536669090667350400000000000000)
      constant := (2665234537676159002998519072640460353541142664396208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree107.table
  base := (84890843342396207962600118467200111033791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-356762220027444807166494025919603331600000000000000)
      constant := (10666221050353294277449720970550531092021743318977776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513915278049422474581/100000000000000000000)
  centralHi := (256957639024711237291/50000000000000000000)
  directionLo := (258166858122611348823/50000000000000000000)
  directionHi := (516333716245222697647/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree108.table
  base := (43730307992322047321569408300125717689963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-29989587282817727906898024247560666000000000000000)
      constant := (904637762816762943997136889762148392809667976409928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree108.table
  base := (34984245880467733751786982258739073891/4000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-119988522257849885390849149177622304000000000000000)
      constant := (3620344434863947549886514180904544130984005709480000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258166858122611348823/50000000000000000000)
  centralHi := (516333716245222697647/100000000000000000000)
  directionLo := (829985407178649171/160000000000000000)
  directionHi := (129685219871663932969/25000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree109.table
  base := (45031557249529781130206353151371159657989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-90769388999378153098851476394696645600000000000000)
      constant := (2763032138579767902627449685026085289428783663690152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree109.table
  base := (90063113340821863826167422351720093757323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-363168913519654505178600869146130492400000000000000)
      constant := (11057606842852896645673228898465878175272633568132528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (829985407178649171/160000000000000000)
  centralHi := (129685219871663932969/25000000000000000000)
  directionLo := (260568462006425492439/50000000000000000000)
  directionHi := (521136924012850984879/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree110.table
  base := (23174584949513747346595700945334890486507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-91570016150303122477008880046711293200000000000000)
      constant := (2812591087804755131032993994660787832767502112914352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree110.table
  base := (46349169376458619640807870379532438524889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-366372260265759354184654290759394072800000000000000)
      constant := (11255941664099721414950456686848578166252427216517408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260568462006425492439/50000000000000000000)
  centralHi := (521136924012850984879/100000000000000000000)
  directionLo := (10470440049750783181/2000000000000000000)
  directionHi := (523522002487539159051/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree111.table
  base := (95366291425897525991947702116441324225003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-30790214433742697285055427899575313600000000000000)
      constant := (954196711964311122299516429315418958705318038066084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree111.table
  base := (95366290482889499024274193019166154862279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-123191869003954734396902570790885884400000000000000)
      constant := (3818679255801809238861765388261126035925142033527248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10470440049750783181/2000000000000000000)
  centralHi := (523522002487539159051/100000000000000000000)
  directionLo := (32868516507035144423/6250000000000000000)
  directionHi := (525896264112562310769/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree112.table
  base := (49033484487561917541728778351107221557993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-93171270452153061233323687350740588400000000000000)
      constant := (2913029282636591620551290350730568324395476941018824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree112.table
  base := (3922678724973242492927624066667097735843/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-372778953757969052196761133985921233600000000000000)
      constant := (11657895151941324346829221935879147108844595254881200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32868516507035144423/6250000000000000000)
  centralHi := (525896264112562310769/100000000000000000000)
  directionLo := (528259854736792231089/100000000000000000000)
  directionHi := (52825985473679223109/10000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree113.table
  base := (5040018604071189542127913959805409472061/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-93971897603078030611481091002755236000000000000000)
      constant := (2963908527850016945791247524073950041821780867582480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree113.table
  base := (100800371313886892471534607781367079029489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-375982300504073901202814555599184814000000000000000)
      constant := (11861513816966507009027365327659561315311024512204304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528259854736792231089/100000000000000000000)
  centralHi := (52825985473679223109/10000000000000000000)
  directionLo := (265306458480341072419/50000000000000000000)
  directionHi := (530612916960682144839/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree114.table
  base := (103566500419067049505854749697006659834461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-31590841584667666663212831551589961200000000000000)
      constant := (1005075957122387686946060351719899902368577757406908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree114.table
  base := (51783249863345280285863422326750956299057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-126395215750059583402955992404149464800000000000000)
      constant := (4022297920606184051350330818912446066212201119420768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265306458480341072419/50000000000000000000)
  centralHi := (530612916960682144839/100000000000000000000)
  directionLo := (33309724389791488143/6250000000000000000)
  directionHi := (532955590236663810289/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree115.table
  base := (53182676848407400190104156051185175643057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-95573151904927969367795898306784531200000000000000)
      constant := (3066987313039566297656232325597403055342826697357576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree115.table
  base := (106365353072284606226719581559797025678049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-382388993996283599214921398825711974800000000000000)
      constant := (12274034985905198333279350895704895996896485933960464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33309724389791488143/6250000000000000000)
  centralHi := (532955590236663810289/100000000000000000000)
  directionLo := (535288010965590034781/100000000000000000000)
  directionHi := (267644005482795017391/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree116.table
  base := (54598465827132574907239282389457142753123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-96373779055852938745953301958799178800000000000000)
      constant := (3119186852734482602652675030712273199094176980960664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree116.table
  base := (54598465545486864391898405795574378160219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-385592340742388448220974820438975555200000000000000)
      constant := (12482937488696910120924689913337551839283759713699168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535288010965590034781/100000000000000000000)
  centralHi := (267644005482795017391/50000000000000000000)
  directionLo := (10752206251788226803/2000000000000000000)
  directionHi := (537610312589411340151/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree117.table
  base := (112061234058586079508742642898606716169429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-32391468735592636041370235203604608800000000000000)
      constant := (1057275496777740703209647051399621020535929767282012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree117.table
  base := (28015308387641206023468304073461661704071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-129598562496164432409009414017413045200000000000000)
      constant := (4231200423240076946417158669918380688204590882815808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10752206251788226803/2000000000000000000)
  centralHi := (537610312589411340151/100000000000000000000)
  directionLo := (6749032821003311977/1250000000000000000)
  directionHi := (539922625680264958161/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree118.table
  base := (57479130350797411401301292134844968328349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-97975033357702877502268109262828474000000000000000)
      constant := (3224906225729660304868273868989100259703692991830632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree118.table
  base := (114958260243452777398089725441948494424103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-391999034234598146233081663665502716000000000000000)
      constant := (12906026328551840302783732414809828465279083286090608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6749032821003311977/1250000000000000000)
  centralHi := (539922625680264958161/100000000000000000000)
  directionLo := (135556269506536114429/25000000000000000000)
  directionHi := (542225078026144457717/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree119.table
  base := (29472002849286720368477169165262980751101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-98775660508627846880425512914843121600000000000000)
      constant := (3278426058828907036453822954217203913960624541833936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree119.table
  base := (58944005492007647905084856052047840654653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-395202380980702995239135085278766296400000000000000)
      constant := (13120212664813242714130505954695500563626927649510816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135556269506536114429/25000000000000000000)
  centralHi := (542225078026144457717/100000000000000000000)
  directionLo := (2127022635598863491/390625000000000000)
  directionHi := (544517794713309053697/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree120.table
  base := (7553155373675113576600996319554051550039/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-33192095886517605419527638855619256400000000000000)
      constant := (1110795329848705537978553387395653395919986725745472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree120.table
  base := (60425242803141985003072567441419742427193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-132801909242269281415062835630676625600000000000000)
      constant := (4445386759388672602978881175398283022659730215259232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2127022635598863491/390625000000000000)
  centralHi := (544517794713309053697/100000000000000000000)
  directionLo := (273400449102791488631/50000000000000000000)
  directionHi := (546800898205582977263/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree121.table
  base := (61922842148868223255122299344875243357223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-100376914810477785636740320218872416800000000000000)
      constant := (3386786017805424025828373497921295669799517163649464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree121.table
  base := (12384568396186224418640867868095672368121/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-401609074472912693251241928505293457200000000000000)
      constant := (13553869168307575462685931890288411816555261944326560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273400449102791488631/50000000000000000000)
  centralHi := (546800898205582977263/100000000000000000000)
  directionLo := (274537254210343579183/50000000000000000000)
  directionHi := (549074508420687158367/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree122.table
  base := (63436803110439594654309721165287414845003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-101177541961402755014897723870887064400000000000000)
      constant := (3441626143538993893893895371206766892000041292556504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree122.table
  base := (126873605918064090767350782344489525388991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-404812421219017542257295350118557037600000000000000)
      constant := (13773339334967360328647120532678542306496258075124976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274537254210343579183/50000000000000000000)
  centralHi := (549074508420687158367/100000000000000000000)
  directionLo := (55133874280373784481/10000000000000000000)
  directionHi := (551338742803737844811/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree123.table
  base := (129934251629242111801021010067360637498713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-33992723037442574797685042507633904000000000000000)
      constant := (1165635455562056735021898743312457058481154160349964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree123.table
  base := (129934251356249971411936626569634627693831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-136005255988374130421116257243940206000000000000000)
      constant := (4664856925967819585119219001777550318839542906437072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55133874280373784481/10000000000000000000)
  centralHi := (551338742803737844811/100000000000000000000)
  directionLo := (553593716398039623859/100000000000000000000)
  directionHi := (27679685819901981193/5000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree124.table
  base := (33256905104107423778682377943329931003507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-102778796263252693771212531174916359600000000000000)
      constant := (3552626687192716132332881612270873842990591814626352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree124.table
  base := (16628452521292394306968387017583757082487/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-411219114711227240269402193345084198400000000000000)
      constant := (14217563496899565306143838370257684143078293215069056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553593716398039623859/100000000000000000000)
  centralHi := (27679685819901981193/5000000000000000000)
  directionLo := (277919770956646794797/50000000000000000000)
  directionHi := (111167908382658717919/20000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree125.table
  base := (17019214060913198656101235322371143347337/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-103579423414177663149369934826931007200000000000000)
      constant := (3608787105010134391109421453850472603960197074546464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree125.table
  base := (68076856132739841120946537299514270423509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-414422461457332089275455614958347778800000000000000)
      constant := (14442317491762270736947719905376426721324773635750048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277919770956646794797/50000000000000000000)
  centralHi := (111167908382658717919/20000000000000000000)
  directionLo := (139519082447833770571/25000000000000000000)
  directionHi := (111615265958267016457/20000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree126.table
  base := (69656263878400300601062112611582059739637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-34793350188367544175842446159648551600000000000000)
      constant := (1221795873365019864003361827081786451758752542047672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree126.table
  base := (27862505511371853730545748710456610660069/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-139208602734478979427169678857203786400000000000000)
      constant := (4889610920772879113297394040708449296037306861998640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139519082447833770571/25000000000000000000)
  centralHi := (111615265958267016457/20000000000000000000)
  directionLo := (560304188269509487399/100000000000000000000)
  directionHi := (2801520941347547437/500000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree127.table
  base := (28500813229769388912124786310640514251021/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-105180677716027601905684742130960302400000000000000)
      constant := (3722428232408714957436035732891880688257445840858820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree127.table
  base := (35626016492160545622050122785284896944441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-420829154949541787287562458184874939600000000000000)
      constant := (14897109308414031180092713219274174585172880066224704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560304188269509487399/100000000000000000000)
  centralHi := (2801520941347547437/500000000000000000)
  directionLo := (140630805860447249003/25000000000000000000)
  directionHi := (562523223441788996013/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree128.table
  base := (72864163797712683459756962650673954704489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (32620705689)
      previous := (0)
      next := (29060990475)
      square := (756943168777855140908582540730568800000000000000)
      linear := (-105981304866952571283842145782974950000000000000000)
      constant := (3779908941916426579452272239938551184501001469502152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree128.table
  base := (1457283274330187588498760675357245181939/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (130516971981)
      previous := (0)
      next := (116209812675)
      square := (3027772675111420563634330162922275200000000000000)
      linear := (-424032501695646636293615879798138520000000000000000)
      constant := (15127147129910183988218808933882569434169964622750400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell137.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140630805860447249003/25000000000000000000)
  centralHi := (562523223441788996013/100000000000000000000)
  directionLo := (564733539317727971807/100000000000000000000)
  directionHi := (17647923103678999119/3125000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree129.table
  base := (74492656017856595844988562945504527326287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252314389592618380302860846910189600000000000000)
      linear := (-35593977339292513553999849811663199200000000000000)
      constant := (1279276582862396373465238413675843182482928209500072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree129.table
  base := (148985311889355598488713916652724451129319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (43505657327)
      previous := (0)
      next := (38736604225)
      square := (1009257558370473521211443387640758400000000000000)
      linear := (-142411949480583828433223100470467366800000000000000)
      constant := (5119648742227820120763766482253034749956823098955728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell137.Kernel129
