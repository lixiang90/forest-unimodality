import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell004.Parameters
import ForestUnimodality.BinomialMassData.Q39_140.Batch000_049
import ForestUnimodality.BinomialMassData.Q39_140.Batch050_099
import ForestUnimodality.BinomialMassData.Q39_140.Batch100_149
import ForestUnimodality.BinomialMassData.Q39_140.Batch150_199
import ForestUnimodality.BinomialMassData.Q2_7.Batch000_049
import ForestUnimodality.BinomialMassData.Q2_7.Batch050_099
import ForestUnimodality.BinomialMassData.Q2_7.Batch100_149
import ForestUnimodality.BinomialMassData.Q2_7.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree000.table
  base := (59605161807453112998622657/10000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (4735356609463665933379417000000000000000)
      constant := (1192103236149062259972453140000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree000.table
  base := (59605161807453112998622657/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (236767830473183296668970850000000000000)
      constant := (59605161807453112998622657000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree001.table
  base := (44270361169726007900186446512645561224489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (145671456171477692112525831760000000000000)
      constant := (43332345184648013829357444106229649999999220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree001.table
  base := (1755243797320012021508671582082393877551/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (7172853555122292376622361330000000000000)
      constant := (2147491583538684972931922411910932499999975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (7134853930393894497/25000000000000000000)
  directionHi := (28539415721575577989/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree002.table
  base := (3295464398032981583288360934128238257653/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (59310438479235753489460230520000000000000)
      constant := (32214391289427681944906101333904734924999400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree002.table
  base := (1295403224142243754280902092715414327551/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (2744083417058603216465151010000000000000)
      constant := (1582770176114178717636035142816382551249975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7134853930393894497/25000000000000000000)
  centralHi := (28539415721575577989/100000000000000000000)
  directionLo := (403608287756561131/1000000000000000000)
  directionHi := (40360828775656113101/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree003.table
  base := (4912269986864642600388302312717015360637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-27050579213006185133605370720000000000000)
      constant := (23984469786800557766418994299146375267121300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree003.table
  base := (23933875809960812081777419372057776433417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-1684686721005085943692059310000000000000)
      constant := (1168509798842859408181484615370831045237433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403608287756561131/1000000000000000000)
  centralHi := (40360828775656113101/100000000000000000000)
  directionLo := (2471585902404944637/5000000000000000000)
  directionHi := (49431718048098892741/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree004.table
  base := (9148180399480559954177240035651815699891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-113411596905248123756670971960000000000000)
      constant := (17864344808676463384870563355869558771786360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree004.table
  base := (1767905539317921173143706018542400511561/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-6113456859068775103849269630000000000000)
      constant := (863137618932000114021598633645776250664890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2471585902404944637/5000000000000000000)
  centralHi := (49431718048098892741/100000000000000000000)
  directionLo := (7134853930393894497/12500000000000000000)
  directionHi := (57078831443151155977/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree005.table
  base := (13584238924410864916374731272608256019061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-199772614597490062379736573200000000000000)
      constant := (13290087458219380597227980584081090898679780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree005.table
  base := (6505907386384950569758966648644229329809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-10542226997132464264006479950000000000000)
      constant := (636822211939972643498683666067134474321282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7134853930393894497/12500000000000000000)
  centralHi := (57078831443151155977/100000000000000000000)
  directionLo := (63816073591569203843/100000000000000000000)
  directionHi := (15954018397892300961/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree006.table
  base := (5016789322335383738232799828279433480829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-286133632289732001002802174440000000000000)
      constant := (9878120182747662464945313783059689622424840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree006.table
  base := (9520815420999316945760778019458456782151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-14970997135196153424163690270000000000000)
      constant := (469407990007832391960035938913464382325399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63816073591569203843/100000000000000000000)
  centralHi := (15954018397892300961/25000000000000000000)
  directionLo := (8738375759378043961/12500000000000000000)
  directionHi := (69907006075024351689/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree007.table
  base := (7325811208651918282866267645643515101999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-7601931632285182441344240320000000000000)
      constant := (149311134820289344252591055649870302039980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree007.table
  base := (3438027328807625141344619124850929536021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-395913617821629440496344910000000000000)
      constant := (7035200444963696426516612309701859072042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8738375759378043961/12500000000000000000)
  centralHi := (69907006075024351689/100000000000000000000)
  directionLo := (75508196562375974161/100000000000000000000)
  directionHi := (37754098281187987081/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree008.table
  base := (261758511710648669963123858473908417061/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-458855667674215878248933376920000000000000)
      constant := (5383212674060409749934951506456604974395600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree008.table
  base := (969122662927598129807171611940740159501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-23828537411323531744478110910000000000000)
      constant := (251408668095133027754412518365481339077745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75508196562375974161/100000000000000000000)
  centralHi := (37754098281187987081/50000000000000000000)
  directionLo := (403608287756561131/500000000000000000)
  directionHi := (80721657551312226201/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree009.table
  base := (3601563224385310273874539412997432277351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-545216685366457816871998978160000000000000)
      constant := (3922130739317108008875188083134483631803980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree009.table
  base := (3266450331567871244042032652297307929537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-28257307549387220904635321230000000000000)
      constant := (181470516919084427288159849422568088547313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403608287756561131/500000000000000000)
  centralHi := (80721657551312226201/100000000000000000000)
  directionLo := (21404561791181683491/25000000000000000000)
  directionHi := (17123649432945346793/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree010.table
  base := (288520293473688118236190936316709449127/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-631577703058699755495064579400000000000000)
      constant := (2818508527212437163601003108923002081155680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree010.table
  base := (1010334810128309950375217298011236055651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-32686077687450910064792531550000000000000)
      constant := (129133459955809987319646952205101133453798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21404561791181683491/25000000000000000000)
  centralHi := (17123649432945346793/20000000000000000000)
  directionLo := (22562389192649169507/25000000000000000000)
  directionHi := (90249556770596678029/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree011.table
  base := (1269534311464929609286375126867990800413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-717938720750941694118130180640000000000000)
      constant := (1988621410644981964211751634107630984404740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree011.table
  base := (255704809394151470513527993821553298199/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-37114847825514599224949741870000000000000)
      constant := (90210351992055801730633182849024446447004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22562389192649169507/25000000000000000000)
  centralHi := (90249556770596678029/100000000000000000000)
  directionLo := (18930906736887240771/20000000000000000000)
  directionHi := (5915908355277262741/6250000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree012.table
  base := (423038920519642113490522990688204969791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-804299738443183632741195781880000000000000)
      constant := (1371081998620639103144365514002440870395180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree012.table
  base := (26347418478295790374957187651073411781/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-41543617963578288385106952190000000000000)
      constant := (61657321078450190138401584199220777418152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18930906736887240771/20000000000000000000)
  centralHi := (5915908355277262741/6250000000000000000)
  directionLo := (2471585902404944637/2500000000000000000)
  directionHi := (98863436096197785481/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree013.table
  base := (-277399765614733645810389036396488526709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-890660756135425571364261383120000000000000)
      constant := (920735869382399998172731832584441243825180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree013.table
  base := (-460771782221762060055137365752910079511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-45972388101641977545264162510000000000000)
      constant := (41253602286837651644483937818107406103961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2471585902404944637/2500000000000000000)
  centralHi := (98863436096197785481/100000000000000000000)
  directionLo := (2058006535118477071/2000000000000000000)
  directionHi := (102900326755923853551/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree014.table
  base := (-865804155564462486764248390381373925731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-19939219874034030816067897640000000000000)
      constant := (12331450254622961785957569440372521485380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree014.table
  base := (-8008153542540967372743420985804930571/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-1028595066116442177661660670000000000000)
      constant := (558610817841273938274221753816968886912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2058006535118477071/2000000000000000000)
  centralHi := (102900326755923853551/100000000000000000000)
  directionLo := (106784715648845615883/100000000000000000000)
  directionHi := (26696178912211403971/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree015.table
  base := (-273482155100821757245849450709885191107/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-1063382791519909448610392585600000000000000)
      constant := (396865782251941401840904385346562563575700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree015.table
  base := (-11769496213453435315719279706467850423/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-54829928377769355865578583150000000000000)
      constant := (18813801216184427261520845181033642146944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106784715648845615883/100000000000000000000)
  centralHi := (26696178912211403971/25000000000000000000)
  directionLo := (55266340900076171571/50000000000000000000)
  directionHi := (110532681800152343143/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree016.table
  base := (-900519404465362631189571894570104909197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-1149743809212151387233458186840000000000000)
      constant := (280167228881537157349399280914594377973880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree016.table
  base := (-961625094620977588024568255290640975519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-59258698515833045025735793470000000000000)
      constant := (14691197464623198634063675141517184399138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55266340900076171571/50000000000000000000)
  centralHi := (110532681800152343143/100000000000000000000)
  directionLo := (7134853930393894497/6250000000000000000)
  directionHi := (114157662886302311953/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree017.table
  base := (-1090404154219153964969581814206575789551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-1236104826904393325856523788080000000000000)
      constant := (240307750823196299606684470648111452480040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree017.table
  base := (-143051798488826243192769484578095447411/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-63687468653896734185893003790000000000000)
      constant := (14341584889343481770429916430773169229776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7134853930393894497/6250000000000000000)
  centralHi := (114157662886302311953/100000000000000000000)
  directionLo := (117671025513469370671/100000000000000000000)
  directionHi := (7354439094591835667/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree018.table
  base := (-157336745746250933016526308113484511423/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-1322465844596635264479589389320000000000000)
      constant := (266832063322023852044748079268562860887360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree018.table
  base := (-653349704268439825533375158044725417593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-68116238791960423346050214110000000000000)
      constant := (17266753931662930276440121063233818151772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117671025513469370671/100000000000000000000)
  centralHi := (7354439094591835667/6250000000000000000)
  directionLo := (1210824863269683393/1000000000000000000)
  directionHi := (121082486326968339301/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree019.table
  base := (-2818902200220282045434799787097626634611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-1408826862288877203102654990560000000000000)
      constant := (351778136009272742345303694901325898081220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree019.table
  base := (-2904673731644934960472435584917253186497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-72545008930024112506207424430000000000000)
      constant := (23088747077958828139583399599054593861647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1210824863269683393/1000000000000000000)
  centralHi := (121082486326968339301/100000000000000000000)
  directionLo := (7775026814877742279/6250000000000000000)
  directionHi := (24880085807608775293/20000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree020.table
  base := (-77289805883838398389209081792649814999/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-1495187879981119141725720591800000000000000)
      constant := (489029669252004849472649507528127252039200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree020.table
  base := (-3168562159305158493376666026418498929719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-76973779068087801666364634750000000000000)
      constant := (31518040979481005623357830705493552443769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7775026814877742279/6250000000000000000)
  centralHi := (24880085807608775293/20000000000000000000)
  directionLo := (127632147183138407687/100000000000000000000)
  directionHi := (15954018397892300961/12500000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree021.table
  base := (-668059579739332766720735347169876196561/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-32276508115782879190791554960000000000000)
      constant := (13751910182050422105856968816012380343900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree021.table
  base := (-681927563729831645167080301680746999471/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-1661276514411254914826976430000000000000)
      constant := (863888233165056628638615231596265002645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127632147183138407687/100000000000000000000)
  centralHi := (15954018397892300961/12500000000000000000)
  directionLo := (130784032833932830383/100000000000000000000)
  directionHi := (8174002052120801899/6250000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree022.table
  base := (-1784405216325827309276876670883588727489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-1667909915365603018971851794280000000000000)
      constant := (902504507460721142055576689276166094121560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree022.table
  base := (-453935053585694914752629907617224808951/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-85831319344215179986679055390000000000000)
      constant := (55350788183356502830938882254047874891208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130784032833932830383/100000000000000000000)
  centralHi := (8174002052120801899/6250000000000000000)
  directionLo := (1673271565957883071/1250000000000000000)
  directionHi := (133861725276630645681/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree023.table
  base := (-945032779372945071556312166066857830071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-1754270933057844957594917395520000000000000)
      constant := (1172071140204949670187882696090917306121680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree023.table
  base := (-3836923899688866658526281514339507771899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-90260089482278869146836265710000000000000)
      constant := (70439973650836450165255629137364119176949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1673271565957883071/1250000000000000000)
  centralHi := (133861725276630645681/100000000000000000000)
  directionLo := (17108778696807347643/12500000000000000000)
  directionHi := (27374045914891756229/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree024.table
  base := (-1988330816898358893690882182988517048303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-1840631950750086896217982996760000000000000)
      constant := (1480189850185072855835579863054506585326120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree024.table
  base := (-2014118867958783082365152289303852816889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-94688859620342558306993476030000000000000)
      constant := (87486874118861806854662747808222423944878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17108778696807347643/12500000000000000000)
  centralHi := (27374045914891756229/20000000000000000000)
  directionLo := (8738375759378043961/6250000000000000000)
  directionHi := (139814012150048703377/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree025.table
  base := (-2080172362500140841739642271417510667251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-1926992968442328834841048598000000000000000)
      constant := (1824956748835952428771803776146679092188040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree025.table
  base := (-4207260249759304657649249316198955114539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-99117629758406247467150686350000000000000)
      constant := (106401412280437878669369336006251199387589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8738375759378043961/6250000000000000000)
  centralHi := (139814012150048703377/100000000000000000000)
  directionLo := (7134853930393894497/5000000000000000000)
  directionHi := (142697078607877889941/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree026.table
  base := (-2166384313255600494842865393732065792549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-2013353986134570773464114199240000000000000)
      constant := (2204815365457033954131991274597151046603960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree026.table
  base := (-2187748465936523480022642572566443931273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-103546399896469936627307896670000000000000)
      constant := (127109819093275389294029092248488494735246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7134853930393894497/5000000000000000000)
  centralHi := (142697078607877889941/100000000000000000000)
  directionLo := (145523037670850579963/100000000000000000000)
  directionHi := (36380759417712644991/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree027.table
  base := (-4495245021257297951114528695473213664053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-2099715003826812712087179800480000000000000)
      constant := (2618480250779051631704985274709250609228060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree027.table
  base := (-2267096780107816229384163762111754710199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-107975170034533625787465106990000000000000)
      constant := (149551051437489208772996159053048038400498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145523037670850579963/100000000000000000000)
  centralHi := (36380759417712644991/25000000000000000000)
  directionLo := (148295154144296678221/100000000000000000000)
  directionHi := (74147577072148339111/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree028.table
  base := (-4648867601590716082606989419755732160741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-44613796357531727565515212280000000000000)
      constant := (62548562985651118713189813196885356785180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree028.table
  base := (-4684390937192097490093726959249065080167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-2293957962706067651992292190000000000000)
      constant := (3544369591739439931199558400750934919833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148295154144296678221/100000000000000000000)
  centralHi := (74147577072148339111/50000000000000000000)
  directionLo := (151016393124751948323/100000000000000000000)
  directionHi := (37754098281187987081/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree029.table
  base := (-599319547401536588923564645296063406097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-2272437039211296589333311002960000000000000)
      constant := (3543111760543772929175041872395862896199520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree029.table
  base := (-2413483107236639045808348299523976737721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-116832710310661004107779527630000000000000)
      constant := (199436014334634467019210255706650279703342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151016393124751948323/100000000000000000000)
  centralHi := (37754098281187987081/25000000000000000000)
  directionLo := (38422364290002494909/25000000000000000000)
  directionHi := (153689457160009979637/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree030.table
  base := (-197323659290784007723106546021039098343/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-2358798056903538527956376604200000000000000)
      constant := (4052412247935035059885027659284542090596500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree030.table
  base := (-620333047731908130889699417902580289513/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-121261480448724693267936737950000000000000)
      constant := (226800259955686491539054255182188526510904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38422364290002494909/25000000000000000000)
  centralHi := (153689457160009979637/100000000000000000000)
  directionLo := (9769801105452825853/6250000000000000000)
  directionHi := (156316817687245213649/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree031.table
  base := (-5065139163397382095784810086124377225973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-2445159074595780466579442205440000000000000)
      constant := (4592128120888642512328084629455110318546460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree031.table
  base := (-5092122504426118672902194563371031498073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-125690250586788382428093948270000000000000)
      constant := (255735630669073674689327562854819456594423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9769801105452825853/6250000000000000000)
  centralHi := (156316817687245213649/100000000000000000000)
  directionLo := (31780148358115871661/20000000000000000000)
  directionHi := (79450370895289679153/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree032.table
  base := (-1038254401369206867499994411525636055493/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-2531520092288022405202507806680000000000000)
      constant := (5161698246839207286873997506212383328084300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree032.table
  base := (-5215888580085645766495726785098483325873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-130119020724852071588251158590000000000000)
      constant := (286215274577705483391293784970174317032223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31780148358115871661/20000000000000000000)
  centralHi := (79450370895289679153/50000000000000000000)
  directionLo := (403608287756561131/250000000000000000)
  directionHi := (161443315102624452401/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree033.table
  base := (-5311984789451985497370839254578348532609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-2617881109980264343825573407920000000000000)
      constant := (5760637744487029375958030393806218438043180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree033.table
  base := (-2667218188816538733203419956110639042141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-134547790862915760748408368910000000000000)
      constant := (318215977010419591858029174241157373870182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403608287756561131/250000000000000000)
  centralHi := (161443315102624452401/100000000000000000000)
  directionLo := (16394646150818322517/10000000000000000000)
  directionHi := (163946461508183225171/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree034.table
  base := (-5427707063046045791395979547693243041211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-2704242127672506282448639009160000000000000)
      constant := (6388525653037914767901586778932621819613220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree034.table
  base := (-5448177247335596646974078626405054213459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-138976561000979449908565579230000000000000)
      constant := (351717581804124039246945041266152343540509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16394646150818322517/10000000000000000000)
  centralHi := (163946461508183225171/100000000000000000000)
  directionLo := (166411960179498874681/100000000000000000000)
  directionHi := (83205980089749437341/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree035.table
  base := (-5538813244523481815274400660267812363399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-56951084599280575940238869600000000000000)
      constant := (143775409059887799977951818219643752732020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree035.table
  base := (-5557469630445529919525691056204692224041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-2926639411000880389157607950000000000000)
      constant := (7891888272192955542917494443795307775959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (166411960179498874681/100000000000000000000)
  centralHi := (83205980089749437341/50000000000000000000)
  directionLo := (168841460371888617493/100000000000000000000)
  directionHi := (84420730185944308747/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree036.table
  base := (-2822815397495653987116753243583433114329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-2876964163056990159694770211640000000000000)
      constant := (7729725005291917551889331518328471095915160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree036.table
  base := (-2831313401223336538686032410672312922713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-147834101277106828228879999870000000000000)
      constant := (423155457111705945053856740314113333574126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168841460371888617493/100000000000000000000)
  centralHi := (84420730185944308747/50000000000000000000)
  directionLo := (21404561791181683491/12500000000000000000)
  directionHi := (171236494329453467929/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree037.table
  base := (-5748446920049549556548151617850565168527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-2963325180749232098317835812880000000000000)
      constant := (8442434075622136044301306557959446134843540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree037.table
  base := (-1440980811514177412026432667041946706311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-152262871415170517389037210190000000000000)
      constant := (461062927473710916747609572399778445563044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21404561791181683491/12500000000000000000)
  centralHi := (171236494329453467929/100000000000000000000)
  directionLo := (173598488587803854029/100000000000000000000)
  directionHi := (17359848858780385403/10000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree038.table
  base := (-5847514114093681304546849870028222748449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-3049686198441474036940901414120000000000000)
      constant := (9182874810417592428673620670300341706519980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree038.table
  base := (-5861599949286220497973947426026215560877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-156691641553234206549194420510000000000000)
      constant := (500413128010951274238100041364715437517027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173598488587803854029/100000000000000000000)
  centralHi := (17359848858780385403/10000000000000000000)
  directionLo := (175928773910633448189/100000000000000000000)
  directionHi := (17592877391063344819/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree039.table
  base := (-1485763697878117694702667386606181830601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-3136047216133715975563967015360000000000000)
      constant := (9950829243577294495636826918680767224044080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree039.table
  base := (-5955868850480174956034219746683355650739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-161120411691297895709351630830000000000000)
      constant := (541195673744523520401510419272515573113789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (175928773910633448189/100000000000000000000)
  centralHi := (17592877391063344819/10000000000000000000)
  directionLo := (4455714851417481549/2500000000000000000)
  directionHi := (178228594056699261961/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree040.table
  base := (-6035265188819926962517184478978180514163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-3222408233825957914187032616600000000000000)
      constant := (10746105063317513441676902947801383096120260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree040.table
  base := (-6046916598596456187721275333808105403263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-165549181829361584869508841150000000000000)
      constant := (583401418875491380131539048643402835240113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4455714851417481549/2500000000000000000)
  centralHi := (178228594056699261961/100000000000000000000)
  directionLo := (22562389192649169507/12500000000000000000)
  directionHi := (180499113541193356057/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree041.table
  base := (-3062159339164252675739136853460576237271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-3308769251518199852810098217840000000000000)
      constant := (11568532364772042880898207299214270574948840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree041.table
  base := (-122698155150489354805653158343099613873/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-169977951967425274029666051470000000000000)
      constant := (627022299773274079613056286719405946011150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22562389192649169507/12500000000000000000)
  centralHi := (180499113541193356057/100000000000000000000)
  directionLo := (182741424528992675851/100000000000000000000)
  directionHi := (45685356132248168963/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree042.table
  base := (-3105184300881605447878355002567792999899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-69288372841029424314962526920000000000000)
      constant := (253427772919395468617126992929288280004040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree042.table
  base := (-6219987554080998468182377087570960275957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-3559320859295693126322923710000000000000)
      constant := (13715330618854060509741340072429039724043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182741424528992675851/100000000000000000000)
  centralHi := (45685356132248168963/25000000000000000000)
  directionLo := (92478276487797988819/50000000000000000000)
  directionHi := (184956552975595977639/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree043.table
  base := (-3146775354102177714236996736671952951093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-3481491286902683730056229420320000000000000)
      constant := (13294257554053813089240878913035972215857720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree043.table
  base := (-6302284247614959259024740893007585588187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-178835492243552652349980472110000000000000)
      constant := (718481835819119402731736084782628306178837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92478276487797988819/50000000000000000000)
  centralHi := (184956552975595977639/100000000000000000000)
  directionLo := (93572732056864937621/50000000000000000000)
  directionHi := (187145464113729875243/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree044.table
  base := (-3186992631367203631035986150998107024817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-3567852304594925668679295021560000000000000)
      constant := (14197304548001529315710164851075710231358680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree044.table
  base := (-1276382236575195692166164160624509380843/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-183264262381616341510137682430000000000000)
      constant := (766308652366353603823255048406995201693465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93572732056864937621/50000000000000000000)
  centralHi := (187145464113729875243/100000000000000000000)
  directionLo := (18930906736887240771/10000000000000000000)
  directionHi := (189309067368872407711/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree045.table
  base := (-6451778878557415178647444101391330800449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-3654213322287167607302360622800000000000000)
      constant := (15126997373953558835192218809561495815559980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree045.table
  base := (-6458968575491535047347092107072446932303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-187693032519680030670294892750000000000000)
      constant := (815526739399805098538305265253450100317153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18930906736887240771/10000000000000000000)
  centralHi := (189309067368872407711/100000000000000000000)
  directionLo := (191448220774707611531/100000000000000000000)
  directionHi := (47862055193676902883/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree046.table
  base := (-1631756528749767942221593919793365828281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-3740574339979409545925426224040000000000000)
      constant := (16083243363770722908814793317002005953138480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree046.table
  base := (-6533545069998357726451035329976921530033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-192121802657743719830452103070000000000000)
      constant := (866131753337174180190890189591130845028383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191448220774707611531/100000000000000000000)
  centralHi := (47862055193676902883/25000000000000000000)
  directionLo := (96781867474659351043/50000000000000000000)
  directionHi := (193563734949318702087/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree047.table
  base := (-6599810875837892069545714982987570998399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-3826935357671651484548491825280000000000000)
      constant := (17065960291750076800556079384705180421568980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree047.table
  base := (-6605719103123665250362538719099904242501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-196550572795807408990609313390000000000000)
      constant := (918119850778827129922235297304104692117451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96781867474659351043/50000000000000000000)
  centralHi := (193563734949318702087/100000000000000000000)
  directionLo := (97828188342188747743/50000000000000000000)
  directionHi := (195656376684377495487/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree048.table
  base := (-6670207636247736518741963167054300145407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-3913296375363893423171557426520000000000000)
      constant := (18075075172221237281061905881534785857501140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree048.table
  base := (-667556009935782946362334462406398430979/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-200979342933871098150766523710000000000000)
      constant := (971487629924735727349795213260864768820290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97828188342188747743/50000000000000000000)
  centralHi := (195656376684377495487/100000000000000000000)
  directionLo := (197726872192395570961/100000000000000000000)
  directionHi := (98863436096197785481/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree049.table
  base := (-336914126089947141192008630664410444163/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-81625661082778272689686184240000000000000)
      constant := (390010677594393334634990234147235822334800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree049.table
  base := (-6743129521400441079580258170711917852329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-4192002307590505863488239470000000000000)
      constant := (20943511818420816888154622169288082147671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197726872192395570961/100000000000000000000)
  centralHi := (98863436096197785481/50000000000000000000)
  directionLo := (49943977512757261479/25000000000000000000)
  directionHi := (199775910051029045917/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree050.table
  base := (-1701023564784904569460035559283707651937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-4086018410748377300417688629000000000000000)
      constant := (20172246829347040001574123222607866004406960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree050.table
  base := (-340424089725168090612031070387223172249/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-209836883209998476471080944350000000000000)
      constant := (1082350531475138806445219356020521291195980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49943977512757261479/25000000000000000000)
  centralHi := (199775910051029045917/100000000000000000000)
  directionLo := (201804143878280565501/100000000000000000000)
  directionHi := (100902071939140282751/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree051.table
  base := (-6867695014917346737640652135309768718047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-4172379428440619239040754230240000000000000)
      constant := (21260194930571904914679906634933426656313940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree051.table
  base := (-858958140107780257882076503309118710607/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-214265653348062165631238154670000000000000)
      constant := (1139840625134705194455567115562825465442056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201804143878280565501/100000000000000000000)
  centralHi := (100902071939140282751/50000000000000000000)
  directionLo := (101906097384031293681/50000000000000000000)
  directionHi := (203812194768062587363/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree052.table
  base := (-1385826227405057132651668350899787805759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-4258740446132861177663819831480000000000000)
      constant := (22374322084864573825615565052439039751780900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree052.table
  base := (-866590274732974875998107051708657378133/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-218694423486125854791395364990000000000000)
      constant := (1198700267909370049928745071970206307771864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101906097384031293681/50000000000000000000)
  centralHi := (203812194768062587363/100000000000000000000)
  directionLo := (205800653511847707101/100000000000000000000)
  directionHi := (102900326755923853551/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree053.table
  base := (-6988443810232208960354647584701722953783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-4345101463825103116286885432720000000000000)
      constant := (23514587931151648306832890714925311505292660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree053.table
  base := (-1398338170412491588551743687008449205081/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-223123193624189543951552575310000000000000)
      constant := (1258927606297966533373818395822929944755155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205800653511847707101/100000000000000000000)
  centralHi := (102900326755923853551/50000000000000000000)
  directionLo := (25971260328616282941/12500000000000000000)
  directionHi := (207770082628930263529/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree054.table
  base := (-7045669636584106606027355445470461657993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-4431462481517345054909951033960000000000000)
      constant := (24680956599428058180776053519230947575166860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree054.table
  base := (-3524302299574535418638132211414148740923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-227551963762253233111709785630000000000000)
      constant := (1320520998031642898265781836841413423389546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25971260328616282941/12500000000000000000)
  centralHi := (207770082628930263529/100000000000000000000)
  directionLo := (26215127278134131883/12500000000000000000)
  directionHi := (41944203645014611013/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree055.table
  base := (-7100841149570834646236024095670682554343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-4517823499209586993533016635200000000000000)
      constant := (25873396206873744522404685881667731096743860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree055.table
  base := (-1775873284705082076021148313348193847757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-231980733900316922271866995950000000000000)
      constant := (1383478987825261304589827550083754005839628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26215127278134131883/12500000000000000000)
  centralHi := (41944203645014611013/20000000000000000000)
  directionLo := (105826985848471489697/50000000000000000000)
  directionHi := (42330794339388595879/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree056.table
  base := (-1788496817469636522872067544762143490461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-93962949324527121064409841560000000000000)
      constant := (552895477779924028192271907987028520763120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree056.table
  base := (-3578191396155016009552748053048269183989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-4824683755885318600653555230000000000000)
      constant := (29546944610987050412771178933903461632022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105826985848471489697/50000000000000000000)
  centralHi := (42330794339388595879/20000000000000000000)
  directionLo := (213569431297691231767/100000000000000000000)
  directionHi := (26696178912211403971/12500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree057.table
  base := (-1441026741910830973522648367297219628137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-4690545534594070870779147837680000000000000)
      constant := (28336378014649681110513401170256623822128700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree057.table
  base := (-1801824222341031997778689795919546162813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-240838274176444300592181416590000000000000)
      constant := (1513483749213404040743648965939768952088652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213569431297691231767/100000000000000000000)
  centralHi := (26696178912211403971/12500000000000000000)
  directionLo := (43093572715451741863/20000000000000000000)
  directionHi := (53866965894314677329/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree058.table
  base := (-226696979079960950993404458630244547267/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-4776906552286312809402213438920000000000000)
      constant := (29606872612452088041646475382323530997706880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree058.table
  base := (-7256256110600493521893106536869682757391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-245267044314507989752338626910000000000000)
      constant := (1580528364300101028356155666133385544887841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43093572715451741863/20000000000000000000)
  centralHi := (53866965894314677329/25000000000000000000)
  directionLo := (27168714338680611597/12500000000000000000)
  directionHi := (217349714709444892777/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree059.table
  base := (-1825379115739235553096782950965126676153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-4863267569978554748025279040160000000000000)
      constant := (30903342281160180935016222203913703429480240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree059.table
  base := (-7303278790468539804479092296632101733953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-249695814452571678912495837230000000000000)
      constant := (1648933232810435284604418715925027015036303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27168714338680611597/12500000000000000000)
  centralHi := (217349714709444892777/100000000000000000000)
  directionLo := (21921541171643475683/10000000000000000000)
  directionHi := (219215411716434756831/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree060.table
  base := (-3673395593679180576681582226790345443883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-4949628587670796686648344641400000000000000)
      constant := (32225769301776521465546393505690922929989320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree060.table
  base := (-1469676237078838667445783905950679798241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-254124584590635368072653047550000000000000)
      constant := (1718697558179536411068984165042083449430955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21921541171643475683/10000000000000000000)
  centralHi := (219215411716434756831/100000000000000000000)
  directionLo := (55266340900076171571/25000000000000000000)
  directionHi := (44213072720060937257/20000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree061.table
  base := (-739014358567994804665943664122561342757/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-5035989605363038625271410242640000000000000)
      constant := (33574137914022507657133441192075898840981400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree061.table
  base := (-1847894427786968479100121990866352944579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-258553354728699057232810257870000000000000)
      constant := (1789820634034653837733214926850194822862516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55266340900076171571/25000000000000000000)
  centralHi := (44213072720060937257/20000000000000000000)
  directionLo := (222899962390000935139/100000000000000000000)
  directionHi := (11144998119500046757/5000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree062.table
  base := (-7431587963820357878401081880606461159069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-5122350623055280563894475843880000000000000)
      constant := (34948434098117457623374734419533668064112380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree062.table
  base := (-464555072062163795270877685693055535643/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-262982124866762746392967468190000000000000)
      constant := (1862301833897800644662438978056644460055888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222899962390000935139/100000000000000000000)
  centralHi := (11144998119500046757/5000000000000000000)
  directionLo := (44943916822276514473/20000000000000000000)
  directionHi := (112359792055691286183/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree063.table
  base := (-1494227409884076642564577216060256790991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-106300237566275969439133498880000000000000)
      constant := (741809089407620299006534346890974320900900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree063.table
  base := (-1868075712941656252679896948206870670541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-5457365204180131337818870990000000000000)
      constant := (39513073511595907359629513467172517317836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44943916822276514473/20000000000000000000)
  centralHi := (112359792055691286183/50000000000000000000)
  directionLo := (45304917937425584497/20000000000000000000)
  directionHi := (113262294843563961243/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree064.table
  base := (-375440108375860429759288620343975601803/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-5295072658439764441140607046360000000000000)
      constant := (37774760664053877886614082223210078204661200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree064.table
  base := (-7509852868630897043451160106209282229891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-271839665142890124713281888830000000000000)
      constant := (2011336445548666782484628626155745170735341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45304917937425584497/20000000000000000000)
  centralHi := (113262294843563961243/50000000000000000000)
  directionLo := (45663065154520924781/20000000000000000000)
  directionHi := (114157662886302311953/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree065.table
  base := (-3772296698289242723368545277656371110667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-5381433676132006379763672647600000000000000)
      constant := (39226770070460608936434029395118512623092680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree065.table
  base := (-301821605240070221079321119075297890769/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-276268435280953813873439099150000000000000)
      constant := (2087888926895900993732527241632760083807975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45663065154520924781/20000000000000000000)
  centralHi := (114157662886302311953/50000000000000000000)
  directionLo := (57523031383296536761/25000000000000000000)
  directionHi := (46018425106637229409/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree066.table
  base := (-1515703941423751890123164431867294401871/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-5467794693824248318386738248840000000000000)
      constant := (40704664809089333031303822512322257430832100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree066.table
  base := (-3789686280881740358427715099776212599407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-280697205419017503033596309470000000000000)
      constant := (2165797657888572361844070305381931165258114) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57523031383296536761/25000000000000000000)
  centralHi := (46018425106637229409/20000000000000000000)
  directionLo := (231855309367951304073/100000000000000000000)
  directionHi := (115927654683975652037/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree067.table
  base := (-3805294542425357614001240196633114240517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-5554155711516490257009803850080000000000000)
      constant := (42208437053941619242466558663992096088586680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree067.table
  base := (-1522271438743577315232125575952792132581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-285125975557081192193753519790000000000000)
      constant := (2245062293919392002627737023231565927517655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231855309367951304073/100000000000000000000)
  centralHi := (115927654683975652037/50000000000000000000)
  directionLo := (233605185584218834159/100000000000000000000)
  directionHi := (2920064819802735427/1250000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree068.table
  base := (-7640808640102801103231575871792909721221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-5640516729208732195632869451320000000000000)
      constant := (43738079836895588212074417447730948473203420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree068.table
  base := (-7641500270950520767440024902906772823019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-289554745695144881353910730110000000000000)
      constant := (2325682529028168080618998604797568131672069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233605185584218834159/100000000000000000000)
  centralHi := (2920064819802735427/1250000000000000000)
  directionLo := (235342051026938741343/100000000000000000000)
  directionHi := (7354439094591835667/3125000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree069.table
  base := (-7669184705039446527790649831785656961243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-5726877746900974134255935052560000000000000)
      constant := (45293586952430099077669608451407056177981860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree069.table
  base := (-3834903669307029509384484274157418811751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-293983515833208570514067940430000000000000)
      constant := (2407658091502419485142163033392572956448402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235342051026938741343/100000000000000000000)
  centralHi := (7354439094591835667/3125000000000000000)
  directionLo := (118533095833289482117/50000000000000000000)
  directionHi := (47413238333315792847/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree070.table
  base := (-961965365005897129956184858654545770163/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-118637525808024817813857156200000000000000)
      constant := (956631691285027690041668379815272676773920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree070.table
  base := (-769628332245507721590206736953238668989/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-6090046652474944074984186750000000000000)
      constant := (50836504897562530567250091630467613310110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118533095833289482117/50000000000000000000)
  centralHi := (47413238333315792847/20000000000000000000)
  directionLo := (238777883148804359309/100000000000000000000)
  directionHi := (23877788314880435931/10000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree071.table
  base := (-7720428310496776907122323062382289446889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-5899599782285458011502066255040000000000000)
      constant := (48482172673640992832242869049682356342048780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree071.table
  base := (-3860466299629013866522030025720880076629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-302841056109335948834382361070000000000000)
      constant := (2575674260000163452242240778739353752490358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238777883148804359309/100000000000000000000)
  centralHi := (23877788314880435931/10000000000000000000)
  directionLo := (120238695654469929971/50000000000000000000)
  directionHi := (240477391308939859943/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree072.table
  base := (-7743305354955910744667968343313546181429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-5985960799977699950125131856280000000000000)
      constant := (50115241965457695816103353554160724742199580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree072.table
  base := (-7743759059245533456078302075134573729287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-307269826247399637994539571390000000000000)
      constant := (2661714460940309327074837481358405887264937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120238695654469929971/50000000000000000000)
  centralHi := (240477391308939859943/100000000000000000000)
  directionLo := (242164972653936678601/100000000000000000000)
  directionHi := (121082486326968339301/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree073.table
  base := (-1552871609161250749669698515295985559773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-6072321817669941888748197457520000000000000)
      constant := (51774156835882424071482367817222670757112300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree073.table
  base := (-776476616135496038677951675709051007407/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-311698596385463327154696781710000000000000)
      constant := (2749109173313070688206083155242565006370570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242164972653936678601/100000000000000000000)
  centralHi := (121082486326968339301/50000000000000000000)
  directionLo := (48768174962863153927/20000000000000000000)
  directionHi := (60960218703578942409/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree074.table
  base := (-1945897485778102928711629068300042856711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-6158682835362183827371263058760000000000000)
      constant := (53458913796051863917630943737775832001692880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree074.table
  base := (-1945989245551452922193245323375832004581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-316127366523527016314853992030000000000000)
      constant := (2837858246364091880618339217778336927102124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48768174962863153927/20000000000000000000)
  centralHi := (60960218703578942409/25000000000000000000)
  directionLo := (15344083560521448421/6250000000000000000)
  directionHi := (245505336968343174737/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree075.table
  base := (-3900502111247585582311240082989966181799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-6245043853054425765994328660000000000000000)
      constant := (55169509733857644564497849397964666283673960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree075.table
  base := (-3900667129739599493160619340177876874633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-320556136661590705475011202350000000000000)
      constant := (2927961545946998434722741062162568066285966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15344083560521448421/6250000000000000000)
  centralHi := (245505336968343174737/100000000000000000000)
  directionLo := (247158590240494463701/100000000000000000000)
  directionHi := (123579295120247231851/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree076.table
  base := (-7816603717677529848404726707640864211453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-6331404870746667704617394261240000000000000)
      constant := (56905941872251228216369309194023953072776060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree076.table
  base := (-977112553793510016770595141829391833201/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-324984906799654394635168412670000000000000)
      constant := (3019418952640315415637005549762878401385208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247158590240494463701/100000000000000000000)
  centralHi := (123579295120247231851/50000000000000000000)
  directionLo := (7775026814877742279/3125000000000000000)
  directionHi := (248800858076087752929/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree077.table
  base := (-3915195479148652755785663813150665991559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-130974814049773666188580813520000000000000)
      constant := (1197310361881378642505608425150973360337640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree077.table
  base := (-313226306620954567417216640669237426551/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-6722728100769756812149502510000000000000)
      constant := (63514905307738444484855432243269064336225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7775026814877742279/3125000000000000000)
  centralHi := (248800858076087752929/100000000000000000000)
  directionLo := (25043235659380453887/10000000000000000000)
  directionHi := (250432356593804538871/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree078.table
  base := (-7842368203513835425276983680115565202077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-6504126906131151581863525463720000000000000)
      constant := (60456305099690469837982753570094746101964540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree078.table
  base := (-7842607899420278482793589084821763438287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-333842447075781772955482833310000000000000)
      constant := (3206395673477330887294379050483733591523937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25043235659380453887/10000000000000000000)
  centralHi := (250432356593804538871/100000000000000000000)
  directionLo := (252053294917672899217/100000000000000000000)
  directionHi := (126026647458836449609/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree079.table
  base := (-245391795996169215087633731707738518693/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-6590487923823393520486591064960000000000000)
      constant := (62270231996580687894576198552462320053787520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree079.table
  base := (-1963188214219525748494257320146489897777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-338271217213845462115640043630000000000000)
      constant := (3301914808317558519827979463311287980035708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252053294917672899217/100000000000000000000)
  centralHi := (126026647458836449609/50000000000000000000)
  directionLo := (253663875489956800107/100000000000000000000)
  directionHi := (63415968872489200027/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree080.table
  base := (-157218011357556857213718400364483541483/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-6676848941515635459109656666200000000000000)
      constant := (64109986654458204655553096694940306467333000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree080.table
  base := (-1572218815368729901285478641150329735933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-342699987351909151275797253950000000000000)
      constant := (3398787689191497399773831244918169214696415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253663875489956800107/100000000000000000000)
  centralHi := (63415968872489200027/25000000000000000000)
  directionLo := (127632147183138407687/50000000000000000000)
  directionHi := (2042114354930214523/800000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree081.table
  base := (-7867459105542006606780226120973972424969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-6763209959207877397732722267440000000000000)
      constant := (65975567491576670618012293780002507023530380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree081.table
  base := (-7867632933348943740410368238020690417539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-347128757489972840435954464270000000000000)
      constant := (3497014248771578266838915713796986169540589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127632147183138407687/50000000000000000000)
  centralHi := (2042114354930214523/800000000000000000)
  directionLo := (256854741494180201893/100000000000000000000)
  directionHi := (128427370747090100947/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree082.table
  base := (-157444290588183756338261862745810302719/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-6849570976900119336355787868680000000000000)
      constant := (67866973092287589720044412301543295166769000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree082.table
  base := (-7872370654101789969337800134952517550511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-351557527628036529596111674590000000000000)
      constant := (3596594426900118711626052427827326640024961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256854741494180201893/100000000000000000000)
  centralHi := (128427370747090100947/50000000000000000000)
  directionLo := (25843540097628082509/10000000000000000000)
  directionHi := (258435400976280825091/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree083.table
  base := (-7875168133176129623020375810956601434713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-6935931994592361274978853469920000000000000)
      constant := (69784202188768153692352314610655530593981260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree083.table
  base := (-3937654168479335300613897074841719048757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-355986297766100218756268884910000000000000)
      constant := (3697528169782151096142354229605511533221814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25843540097628082509/10000000000000000000)
  centralHi := (258435400976280825091/100000000000000000000)
  directionLo := (260006451319000866269/100000000000000000000)
  directionHi := (26000645131900086627/10000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree084.table
  base := (-7876321076271350006065936298761864422497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-143312102291522514563304470840000000000000)
      constant := (1463821502954661528848804403952762711550060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree084.table
  base := (-7876446964522235666813587548113703211733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-7355409549064569549314818270000000000000)
      constant := (77547253658574399364936581491886296788267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260006451319000866269/100000000000000000000)
  centralHi := (26000645131900086627/10000000000000000000)
  directionLo := (261568065667865660767/100000000000000000000)
  directionHi := (8174002052120801899/3125000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree085.table
  base := (-984459299823658231356297192705952258949/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-7108654029976845152224984672400000000000000)
      constant := (73696126441221844836657124968510334289839840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree085.table
  base := (-7875787417077507647810935356604045705609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-364843838042227597076583305550000000000000)
      constant := (3903456162230136028240595222026401760425159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261568065667865660767/100000000000000000000)
  centralHi := (8174002052120801899/3125000000000000000)
  directionLo := (131560206015114804023/50000000000000000000)
  directionHi := (263120412030229608047/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree086.table
  base := (-7873229033588996583729618183631699858347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-7195015047669087090848050273640000000000000)
      constant := (75690819663308506423720641863992934138819940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree086.table
  base := (-3936665242028228506399206600683781541799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-369272608180291286236740515870000000000000)
      constant := (4008450329979955921258112210692989408903698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131560206015114804023/50000000000000000000)
  centralHi := (263120412030229608047/100000000000000000000)
  directionLo := (132331826743122073019/50000000000000000000)
  directionHi := (264663653486244146039/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree087.table
  base := (-7868985819939886717105790387279624717321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-7281376065361329029471115874880000000000000)
      constant := (77711332489142442052627876960818967777025420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree087.table
  base := (-7869076874198931577656656306723997916627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-373701378318354975396897726190000000000000)
      constant := (4114797897791352704956292333110524102085277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132331826743122073019/50000000000000000000)
  centralHi := (264663653486244146039/100000000000000000000)
  directionLo := (26619794838881765579/10000000000000000000)
  directionHi := (266197948388817655791/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree088.table
  base := (-491434094492218915308276994527188923033/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-7367737083053570968094181476120000000000000)
      constant := (79757664179574756657304363254341677686842560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree088.table
  base := (-1572605444911745646538254358008666420017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-378130148456418664557054936510000000000000)
      constant := (4222498834448690331710160840527876727095835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26619794838881765579/10000000000000000000)
  centralHi := (266197948388817655791/100000000000000000000)
  directionLo := (1673271565957883071/625000000000000000)
  directionHi := (267723450553261291361/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree089.table
  base := (-785510878839983652660760114941113494559/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-7454098100745812906717247077360000000000000)
      constant := (81829814069181537921540003522054087753321800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree089.table
  base := (-7855182108486595241244152054353508787967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-382558918594482353717212146830000000000000)
      constant := (4331553111857782136615965005196678069389617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1673271565957883071/625000000000000000)
  centralHi := (267723450553261291361/100000000000000000000)
  directionLo := (134620154718631803877/50000000000000000000)
  directionHi := (53848061887452721551/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree090.table
  base := (-7845476261473436703307646598880971498719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-7540459118438054845340312678600000000000000)
      constant := (83927781558241448470981976233296647931255380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree090.table
  base := (-1569108408541379250028971705060596258759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-386987688732546042877369357150000000000000)
      constant := (4441960704699134300979056317260153916604045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134620154718631803877/50000000000000000000)
  centralHi := (53848061887452721551/20000000000000000000)
  directionLo := (67687167577947508521/25000000000000000000)
  directionHi := (54149734062358006817/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree091.table
  base := (-7834048483292955673562815217265320213373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-155649390533271362938028128160000000000000)
      constant := (1756154410318403446062666109607693595732540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree091.table
  base := (-7834107493591331134734838241109758954401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-7988090997359382286480134030000000000000)
      constant := (92933093675929255732810283098890241045599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67687167577947508521/25000000000000000000)
  centralHi := (54149734062358006817/20000000000000000000)
  directionLo := (54449734884692061083/20000000000000000000)
  directionHi := (34031084302932538177/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree092.table
  base := (-312833038110598564979827202513239346893/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-7713181153822538722586443881080000000000000)
      constant := (88201167222334059806425871337393636001121500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree092.table
  base := (-488804930170081065104028206264528890259/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-395845229008673421197683777790000000000000)
      constant := (4666835747464491366216040024128609350036944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54449734884692061083/20000000000000000000)
  centralHi := (34031084302932538177/12500000000000000000)
  directionLo := (17108778696807347643/6250000000000000000)
  directionHi := (273740459148917562289/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree093.table
  base := (-7805809121263646019293222160500294644051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-7799542171514780661209509482320000000000000)
      constant := (90376584466091621035124430728722711248830020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree093.table
  base := (-487866036988750701312223365464336173143/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-400273999146737110357840988110000000000000)
      constant := (4781303158026570161651032843015960440255888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17108778696807347643/6250000000000000000)
  centralHi := (273740459148917562289/100000000000000000000)
  directionLo := (275224158141666626479/100000000000000000000)
  directionHi := (3440301976770832831/1250000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree094.table
  base := (-3894499198876004085942845318958995824861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-7885903189207022599832575083560000000000000)
      constant := (92577817436090705865514673399672368183272440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree094.table
  base := (-7789040967126251121512387032588165082983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-404702769284800799517998198430000000000000)
      constant := (4897123804841069822222257452163179910933833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275224158141666626479/100000000000000000000)
  centralHi := (3440301976770832831/1250000000000000000)
  directionLo := (276699901471825673051/100000000000000000000)
  directionHi := (69174975367956418263/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree095.table
  base := (-7770394153337368521812738812932003757409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-7972264206899264538455640684800000000000000)
      constant := (94804865768646142716847739098751636317739180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree095.table
  base := (-1942608080818340019493809872968761683591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-409131539422864488678155408750000000000000)
      constant := (5014297672490956524526456768398122710016164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276699901471825673051/100000000000000000000)
  centralHi := (69174975367956418263/25000000000000000000)
  directionLo := (34770976969900609943/12500000000000000000)
  directionHi := (55633563151840975909/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree096.table
  base := (-968749590665500806677730897060136988117/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-8058625224591506477078706286040000000000000)
      constant := (97057729133199737792463096944840526013162720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree096.table
  base := (-7750030946729897695386710810657629989151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-413560309560928177838312619070000000000000)
      constant := (5132824746939270847918504392037776130531601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34770976969900609943/12500000000000000000)
  centralHi := (55633563151840975909/20000000000000000000)
  directionLo := (8738375759378043961/3125000000000000000)
  directionHi := (279628024300097406753/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree097.table
  base := (-7727806420818855813074924102717599138137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-8144986242283748415701771887280000000000000)
      constant := (99336407228786695922926076731269752844625740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree097.table
  base := (-3863918549425937761825010401428391018171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-417989079698991866998469829390000000000000)
      constant := (5252705015379568226453142552200017680219242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8738375759378043961/3125000000000000000)
  centralHi := (279628024300097406753/100000000000000000000)
  directionLo := (281080647188142038891/100000000000000000000)
  directionHi := (70270161797035509723/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree098.table
  base := (-7703823519939898881584067960005587343009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-167986678775020211312751785480000000000000)
      constant := (2074304077161048866796751470551888253139820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree098.table
  base := (-7703851018590815864204700750009020900349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-8620772445654195023645449790000000000000)
      constant := (109672213593943348313466004409990979099651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281080647188142038891/100000000000000000000)
  centralHi := (70270161797035509723/25000000000000000000)
  directionLo := (282525801429592791701/100000000000000000000)
  directionHi := (141262900714796395851/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree099.table
  base := (-3839024139335695243524766973356700824193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-8317708277668232292947903089760000000000000)
      constant := (103971206538649263711269082827757866384581720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree099.table
  base := (-7678072924896820461568500271679874890101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-426846619975119245318784250030000000000000)
      constant := (5496525088381683385157209652347686130385051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282525801429592791701/100000000000000000000)
  centralHi := (141262900714796395851/50000000000000000000)
  directionLo := (56792720210661722313/20000000000000000000)
  directionHi := (141981800526654305783/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree100.table
  base := (-7650480931405128422308852988591359945647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-8404069295360474231570968691000000000000000)
      constant := (106327327272356341800630078736180467253265940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree100.table
  base := (-3825251509425680961963395669581867247567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-431275390113182934478941460350000000000000)
      constant := (5620464872361954022044185634380977009738434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56792720210661722313/20000000000000000000)
  centralHi := (141981800526654305783/50000000000000000000)
  directionLo := (285394157215755779881/100000000000000000000)
  directionHi := (142697078607877889941/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree101.table
  base := (-3810560846601310351371472594585506324577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-8490430313052716170194034292240000000000000)
      constant := (108709261771252350886050508080849407603829080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree101.table
  base := (-381057074278027400958187032346385847953/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-435704160251246623639098670670000000000000)
      constant := (5745757808973836697394437994160541869006060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285394157215755779881/100000000000000000000)
  centralHi := (142697078607877889941/50000000000000000000)
  directionLo := (28681757830129666261/10000000000000000000)
  directionHi := (286817578301296662611/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree102.table
  base := (-303598830472364838362491393487206411127/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-8576791330744958108817099893480000000000000)
      constant := (111117009841546942409434106058811442927388500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree102.table
  base := (-7589988495836099077721452365563307079169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-440132930389310312799255880990000000000000)
      constant := (5872403889847557115016303627327397953120719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28681757830129666261/10000000000000000000)
  centralHi := (286817578301296662611/100000000000000000000)
  directionLo := (57646794003604175253/20000000000000000000)
  directionHi := (144116985009010438133/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree103.table
  base := (-1889257079861764050226146211099000969953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-8663152348437200047440165494720000000000000)
      constant := (113550571304662137901335914016524916197784240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree103.table
  base := (-7557044207688169851800303923931919246229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-444561700527374001959413091310000000000000)
      constant := (6000403107240617692051964039867335956934779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57646794003604175253/20000000000000000000)
  centralHi := (144116985009010438133/50000000000000000000)
  directionLo := (289643435489358661707/100000000000000000000)
  directionHi := (72410858872339665427/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree104.table
  base := (-7522294534413308147372531596915527540357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-8749513366129441986063231095960000000000000)
      constant := (116009945995666993277035299295614783010450140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree104.table
  base := (-1880577191912848374284886826282795742199/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-448990470665437691119570301630000000000000)
      constant := (6129755453972821403870195884608572034528996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289643435489358661707/100000000000000000000)
  centralHi := (72410858872339665427/25000000000000000000)
  directionLo := (145523037670850579963/50000000000000000000)
  directionHi := (291046075341701159927/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree105.table
  base := (-1497153912500417500972360413962984970177/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-180323967016769059687475442800000000000000)
      constant := (2418268035956799633556418335928701502982300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree105.table
  base := (-748578231196308626322834228272772628741/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-9253453893949007760810765550000000000000)
      constant := (127764508640174280698898578217272273712590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145523037670850579963/50000000000000000000)
  centralHi := (291046075341701159927/100000000000000000000)
  directionLo := (58488397557647654611/20000000000000000000)
  directionHi := (9138812118382446033/3125000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree106.table
  base := (-3723726774136360977638462648042563162299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-8922235401513925863309362298440000000000000)
      constant := (121006134461642563074757073058868576201893960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree106.table
  base := (-3723732483805195522346136976903462515497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-457848010941565069439884722270000000000000)
      constant := (6392519509205402741342813714223460673481294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58488397557647654611/20000000000000000000)
  centralHi := (9138812118382446033/3125000000000000000)
  directionLo := (36728908588651472669/12500000000000000000)
  directionHi := (293831268709211781353/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree107.table
  base := (-925918328272441176461351663428789377471/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-9008596419206167801932427899680000000000000)
      constant := (123542947963179904813701569299631291280627360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree107.table
  base := (-59258854826089794519401645427014320139/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-462276781079628758600041932590000000000000)
      constant := (6525931205668682457964246724699537289148625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36728908588651472669/12500000000000000000)
  centralHi := (293831268709211781353/100000000000000000000)
  directionLo := (922543786652404041/312500000000000000)
  directionHi := (295214011728769293121/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree108.table
  base := (-7365448921579038281696870467869030746743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-9094957436898409740555493500920000000000000)
      constant := (126105574143645809421656450906056349868191860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree108.table
  base := (-460341130005762245412044266573162159169/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-466705551217692447760199142910000000000000)
      constant := (6660696007310725021329716394446640867211504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (922543786652404041/312500000000000000)
  centralHi := (295214011728769293121/100000000000000000000)
  directionLo := (148295154144296678221/50000000000000000000)
  directionHi := (296590308288593356443/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree109.table
  base := (-3660880275814059687723453962898242445821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-9181318454590651679178559102160000000000000)
      constant := (128694012888226543504672942952716444806190840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree109.table
  base := (-7321768752525169840509507887852453378821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-471134321355756136920356353230000000000000)
      constant := (6796813909014859097359301140955229784437771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148295154144296678221/50000000000000000000)
  centralHi := (296590308288593356443/100000000000000000000)
  directionLo := (148980123859234796499/50000000000000000000)
  directionHi := (297960247718469592999/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree110.table
  base := (-7276281626085086002533649244958071108081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-9267679472282893617801624703400000000000000)
      constant := (131308264089358960019350176347141090314080620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree110.table
  base := (-727628896888280390766408179860515001961/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-475563091493819826080513563550000000000000)
      constant := (6934284905963274451354565578868347649039110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148980123859234796499/50000000000000000000)
  centralHi := (297960247718469592999/100000000000000000000)
  directionLo := (299323917303947964299/100000000000000000000)
  directionHi := (2993239173039479643/1000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree111.table
  base := (-7229012248024478658275817225175130840171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-9354040489975135556424690304640000000000000)
      constant := (133948327646030009280275802745505371776632420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree111.table
  base := (-57832150575777830250102856810186695927/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-479991861631883515240670773870000000000000)
      constant := (7073108993608421681308394780097606487447125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299323917303947964299/100000000000000000000)
  centralHi := (2993239173039479643/1000000000000000000)
  directionLo := (150340701175621097039/50000000000000000000)
  directionHi := (300681402351242194079/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree112.table
  base := (-7179952514475059791414062075671235357987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-192661255258517908062199100120000000000000)
      constant := (2788044968635744981381305815158575292840260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree112.table
  base := (-7179958399604982518802409972064781512669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-9886135342243820497976081310000000000000)
      constant := (147209921788725212702111357387935218487331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150340701175621097039/50000000000000000000)
  centralHi := (300681402351242194079/100000000000000000000)
  directionLo := (151016393124751948323/50000000000000000000)
  directionHi := (302032786249503896647/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree113.table
  base := (-712910251698948584320525443300406393193/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-9526762525359619433670821507120000000000000)
      constant := (139305891451001841129142989715109017346708600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree113.table
  base := (-445569236566274567160122205396307350713/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-488849401908010893560985194510000000000000)
      constant := (7354816423999928604880069245709295037041008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151016393124751948323/50000000000000000000)
  centralHi := (302032786249503896647/100000000000000000000)
  directionLo := (37922268816325006657/12500000000000000000)
  directionHi := (303378150530600053257/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree114.table
  base := (-3538231171076591638573935410263822084059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-9613123543051861372293887108360000000000000)
      constant := (142023391524727302470424310069634908715244360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree114.table
  base := (-3538233528749391032016218495487307616821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-493278172046074582721142404830000000000000)
      constant := (7497699758786745469579176727802243853551542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37922268816325006657/12500000000000000000)
  centralHi := (303378150530600053257/100000000000000000000)
  directionLo := (304717574926515094573/100000000000000000000)
  directionHi := (152358787463257547287/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree115.table
  base := (-877754009004889943779899920736125316123/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-9699484560744103310916952709600000000000000)
      constant := (144766703603896380003670603641253777521595680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree115.table
  base := (-3511018146165068921643241410726414307453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-497706942184138271881299615150000000000000)
      constant := (7641936168312896587053220199248811397869606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304717574926515094573/100000000000000000000)
  centralHi := (152358787463257547287/50000000000000000000)
  directionLo := (306051137424491948109/100000000000000000000)
  directionHi := (30605113742449194811/10000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree116.table
  base := (-6965811784614417245281157288375855730057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-9785845578436345249540018310840000000000000)
      constant := (147535827612101293597735991555063661384544140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree116.table
  base := (-5572652449234610725180673487882493669/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-502135712322201961041456825470000000000000)
      constant := (7787525649050930610588763955027197262773750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306051137424491948109/100000000000000000000)
  centralHi := (30605113742449194811/10000000000000000000)
  directionLo := (38422364290002494909/12500000000000000000)
  directionHi := (307378914320019959273/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree117.table
  base := (-6907801554104099523710648882385754373433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-9872206596128587188163083912080000000000000)
      constant := (150330763476601520554412307602554960714035660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree117.table
  base := (-3453902466999917701281755791716706057003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-506564482460265650201614035790000000000000)
      constant := (7934468197626625384386621118751762806413706) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38422364290002494909/12500000000000000000)
  centralHi := (307378914320019959273/100000000000000000000)
  directionLo := (308700980267771560651/100000000000000000000)
  directionHi := (77175245066942890163/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree118.table
  base := (-1369600290263333691874054298559638669633/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-9958567613820829126786149513320000000000000)
      constant := (153151511128004728841333806385745770518798300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree118.table
  base := (-6848004475697306328526855889103977912297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-510993252598329339361771246110000000000000)
      constant := (8082763810806105736094900859473905082297447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308700980267771560651/100000000000000000000)
  centralHi := (77175245066942890163/25000000000000000000)
  directionLo := (310017408330583916129/100000000000000000000)
  directionHi := (31001740833058391613/10000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree119.table
  base := (-339320577196784824580951457081290747509/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-204998543500266756436922757440000000000000)
      constant := (3183634091836347295263850284960483700996400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree119.table
  base := (-271456570000165409953102724862207738481/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-10518816790538633235141397070000000000000)
      constant := (168008418071108513705203677618444806537975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310017408330583916129/100000000000000000000)
  centralHi := (31001740833058391613/10000000000000000000)
  directionLo := (62265654005315295327/20000000000000000000)
  directionHi := (77832067506644119159/25000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree120.table
  base := (-6723031896781147919293584969925927081293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-10131289649205313004032280715800000000000000)
      constant := (158870441529006821421336950456272591460332860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree120.table
  base := (-1680758579467609161605876679676966425151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-519850792874456717682085666750000000000000)
      constant := (8383414218674704081101924086783314580670404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62265654005315295327/20000000000000000000)
  centralHi := (77832067506644119159/25000000000000000000)
  directionLo := (9769801105452825853/3125000000000000000)
  directionHi := (312633635374490427297/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree121.table
  base := (-208058205376366736991302408811786558123/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-10217650666897554942655346317040000000000000)
      constant := (161768624154135242117057482523179373537262720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree121.table
  base := (-6657864738016786406787691627486331233569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-524279563012520406842242877070000000000000)
      constant := (8535769007499958246347554532513169769555119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9769801105452825853/3125000000000000000)
  centralHi := (312633635374490427297/100000000000000000000)
  directionLo := (313933572937331357869/100000000000000000000)
  directionHi := (31393357293733135787/10000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree122.table
  base := (-6590903629495251917833871193326313596779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-10304011684589796881278411918280000000000000)
      constant := (164692618316789922970818305762548212675156580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree122.table
  base := (-1318181113420722663316748761667380944213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-528708333150584096002400087390000000000000)
      constant := (8689476849183718656745354113431491668667815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313933572937331357869/100000000000000000000)
  centralHi := (31393357293733135787/10000000000000000000)
  directionLo := (78807037466098032003/25000000000000000000)
  directionHi := (315228149864392128013/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree123.table
  base := (-652215512667748826771726177374646568119/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-10390372702282038819901477519520000000000000)
      constant := (167642423960579908463454067594001463632433800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree123.table
  base := (-6522156859883329255393898343789958034627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-533137103288647785162557297710000000000000)
      constant := (8844537741043117130195793310494292056303277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78807037466098032003/25000000000000000000)
  centralHi := (315228149864392128013/100000000000000000000)
  directionLo := (158258715965864403053/50000000000000000000)
  directionHi := (316517431931728806107/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree124.table
  base := (-6451617119072067289647948582241214369261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-10476733719974280758524543120760000000000000)
      constant := (170618041031133208391814190253715609918124220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree124.table
  base := (-6451618669337107426917425068791087315781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-537565873426711474322714508030000000000000)
      constant := (9000951680482076179717607901789236721526731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158258715965864403053/50000000000000000000)
  centralHi := (316517431931728806107/100000000000000000000)
  directionLo := (31780148358115871661/10000000000000000000)
  directionHi := (317801483581158716611/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree125.table
  base := (-6379289660253256261664373793419161078219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-10563094737666522697147608722000000000000000)
      constant := (173619469475947040823421000410574222143345380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree125.table
  base := (-1275858209359600386450188995731835146939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-541994643564775163482871718350000000000000)
      constant := (9158718664985276154357063458545700388999945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31780148358115871661/10000000000000000000)
  centralHi := (317801483581158716611/100000000000000000000)
  directionLo := (159540183978923009609/50000000000000000000)
  directionHi := (319080367957846019219/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree126.table
  base := (-3152586401012800372507199879484206223391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-217335831742015604811646414760000000000000)
      constant := (3605034882535774512413297815508631751064360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree126.table
  base := (-15762935105154776396861938617571163721/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-11151498238833445972306712830000000000000)
      constant := (190159973308422817602734580192971534511600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159540183978923009609/50000000000000000000)
  centralHi := (319080367957846019219/100000000000000000000)
  directionLo := (320354146946536847651/100000000000000000000)
  directionHi := (80088536736634211913/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree127.table
  base := (-1557316648637003751752039751195438046479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-10735816773051006574393739924480000000000000)
      constant := (179699760286895203264342038026386882857802320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree127.table
  base := (-3114633851743856516323662683223859762079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-550852183840902541803186138990000000000000)
      constant := (9478311759494816797662228778784061743316258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320354146946536847651/100000000000000000000)
  centralHi := (80088536736634211913/25000000000000000000)
  directionLo := (64324576241300568443/20000000000000000000)
  directionHi := (40202860150812855277/12500000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree128.table
  base := (-6151571086445785146985019983009393386893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-10822177790743248513016805525720000000000000)
      constant := (182778622556221016914339754526858794480844860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree128.table
  base := (-6151572078087766672666997831058224905323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-555280953978966230963343349310000000000000)
      constant := (9640137864827966851125054754918146979639173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64324576241300568443/20000000000000000000)
  centralHi := (40202860150812855277/12500000000000000000)
  directionLo := (322886630205248904801/100000000000000000000)
  directionHi := (161443315102624452401/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree129.table
  base := (-1518021581227945110052900323614175313991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-10908538808435490451639871126960000000000000)
      constant := (185883296005981380168483456232549432769155280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree129.table
  base := (-6072087211609808179597745637168806090867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-559709724117029920123500559630000000000000)
      constant := (9803317005870529124583568670838728501547517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322886630205248904801/100000000000000000000)
  centralHi := (161443315102624452401/50000000000000000000)
  directionLo := (162072726125519087657/50000000000000000000)
  directionHi := (64829090450207635063/20000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree130.table
  base := (-5990812355798025799304210722407987986369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-10994899826127732390262936728200000000000000)
      constant := (189013780591241308612409161515840171773358380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree130.table
  base := (-5990813148611192251151927485415356790041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-564138494255093609283657769950000000000000)
      constant := (9967849180439193237849864950214647517287991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162072726125519087657/50000000000000000000)
  centralHi := (64829090450207635063/20000000000000000000)
  directionLo := (13015976180971382521/4000000000000000000)
  directionHi := (162699702262142281513/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree131.table
  base := (-1181549844739732293311732743081575149677/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-11081260843819974328886002329440000000000000)
      constant := (192170076268298544808666971237157281766582700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree131.table
  base := (-1181549986505258618238711771885784897617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-568567264393157298443814980270000000000000)
      constant := (10133734386405674854934606834347982700083835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13015976180971382521/4000000000000000000)
  centralHi := (162699702262142281513/50000000000000000000)
  directionLo := (163324271553930327191/50000000000000000000)
  directionHi := (326648543107860654383/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree132.table
  base := (-1164579394405040666312364941946979562959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-11167621861512216267509067930680000000000000)
      constant := (195352182994609803185461758248947800141500900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree132.table
  base := (-727862200715975269544554174489376094343/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-572996034531220987603972190590000000000000)
      constant := (10300972621693712094462738435040164571017544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163324271553930327191/50000000000000000000)
  centralHi := (326648543107860654383/100000000000000000000)
  directionLo := (16394646150818322517/5000000000000000000)
  directionHi := (327892923016366450341/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree133.table
  base := (-358515977692182315703668135508112103593/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-229673119983764453186370072080000000000000)
      constant := (4052246953647423742836478081994404126850240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree133.table
  base := (-5736256209582573293471707506095162016967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-11784179687128258709472028590000000000000)
      constant := (213664569066863859549786389553904837983033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16394646150818322517/5000000000000000000)
  centralHi := (327892923016366450341/100000000000000000000)
  directionLo := (1645662991122010761/500000000000000000)
  directionHi := (329132598224402152201/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree134.table
  base := (-1129565055618606008609897158712266056301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-11340343896896700144755199133160000000000000)
      constant := (201793829430220102580191753354581896324125100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree134.table
  base := (-1411956446125648391518479686900006142231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-581853574807348365924286611230000000000000)
      constant := (10639508172173338559251798453327598796122724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1645662991122010761/500000000000000000)
  centralHi := (329132598224402152201/100000000000000000000)
  directionLo := (1032398817793394083/312500000000000000)
  directionHi := (330367621693886106561/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree135.table
  base := (-347350369833089136844086915450549786483/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-11426704914588942083378264734400000000000000)
      constant := (205053369059653934524154984779560379347946560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree135.table
  base := (-2778803184995796741425974575024091453911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-586282344945412055084443821550000000000000)
      constant := (10810805483449057623473779311147639037516722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1032398817793394083/312500000000000000)
  centralHi := (330367621693886106561/100000000000000000000)
  directionLo := (165799022700228514713/50000000000000000000)
  directionHi := (331598045400457029427/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree136.table
  base := (-5465597600090397637408751157888940348327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-11513065932281184022001330335640000000000000)
      constant := (208338719578505092927030420792420838458639540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree136.table
  base := (-2732799002343876541017277992797994286747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-590711115083475744244601031870000000000000)
      constant := (10983455816210215488732266555265796559898794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165799022700228514713/50000000000000000000)
  centralHi := (331598045400457029427/100000000000000000000)
  directionLo := (332823920358997749363/100000000000000000000)
  directionHi := (83205980089749437341/25000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree137.table
  base := (-5371800364785965418011647539837521544963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-11599426949973425960624395936880000000000000)
      constant := (211649880949131757178191022783212228885936260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree137.table
  base := (-1074360145280581911597409641695912710701/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-595139885221539433404758242190000000000000)
      constant := (11157459168604032132503360046924501385878255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (332823920358997749363/100000000000000000000)
  centralHi := (83205980089749437341/25000000000000000000)
  directionLo := (41755662081039491611/12500000000000000000)
  directionHi := (334045296648315932889/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree138.table
  base := (-1319053562243306223080725954475753722687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-11685787967665667899247461538120000000000000)
      constant := (214986853134727973823848143207583045407066960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree138.table
  base := (-2638107286079313549891573582983663191097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-599568655359603122564915452510000000000000)
      constant := (11332815538816450909522447440107601007272494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41755662081039491611/12500000000000000000)
  centralHi := (334045296648315932889/100000000000000000000)
  directionLo := (10476944482344236741/3125000000000000000)
  directionHi := (335262223435015575713/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree139.table
  base := (-258941964469806123206266468571377059823/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-11772148985357909837870527139360000000000000)
      constant := (218349636099284675388294628873778009627469200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree139.table
  base := (-323677473638715605671729759770346549627/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-603997425497666811725072662830000000000000)
      constant := (11509524925070509164606612393200048305092432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10476944482344236741/3125000000000000000)
  centralHi := (335262223435015575713/100000000000000000000)
  directionLo := (42059343624573931877/12500000000000000000)
  directionHi := (336474748996591455017/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree140.table
  base := (-5079675522022025919328468957457042064539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-242010408225513301561093729400000000000000)
      constant := (4525269996072527376353859712650859158709220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree140.table
  base := (-5079675780123622212296545625384105686201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-12416861135423071446637344350000000000000)
      constant := (238522190318874140787070924374615894313799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42059343624573931877/12500000000000000000)
  centralHi := (336474748996591455017/100000000000000000000)
  directionLo := (168841460371888617493/50000000000000000000)
  directionHi := (337682920743777234987/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree141.table
  base := (-4978722982075411534656139815645119265667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-11944871020742393715116658341840000000000000)
      constant := (225152634225015485231792293451064783119646340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree141.table
  base := (-4978723212711533790659900706263325796723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-612854965773794190045387083470000000000000)
      constant := (11867002738772243044216759032053097035960573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168841460371888617493/50000000000000000000)
  centralHi := (337682920743777234987/100000000000000000000)
  directionLo := (338886785242176495379/100000000000000000000)
  directionHi := (16944339262108824769/5000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree142.table
  base := (-4875981704068956210489717744736804531379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-12031232038434635653739723943080000000000000)
      constant := (228592849317847183397280383184525931559248580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree142.table
  base := (-4875981910152109465503457868334110842323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-617283735911857879205544293790000000000000)
      constant := (12047771162838462274613843499291628568726173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338886785242176495379/100000000000000000000)
  centralHi := (16944339262108824769/5000000000000000000)
  directionLo := (340086388233204605819/100000000000000000000)
  directionHi := (17004319411660230291/5000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree143.table
  base := (-954290344366458368304817579298846211247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-12117593056126877592362789544320000000000000)
      constant := (232058875052895896681002407671548653564889700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree143.table
  base := (-4771451905967351541746379431161242471117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-621712506049921568365701504110000000000000)
      constant := (12229892596180912476816689742413099118915267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340086388233204605819/100000000000000000000)
  centralHi := (17004319411660230291/5000000000000000000)
  directionLo := (341281774654368092641/100000000000000000000)
  directionHi := (170640887327184046321/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree144.table
  base := (-583141633567331439666406812709769947927/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-12203954073819119530985855145560000000000000)
      constant := (235550711397651856655177802765987403608252320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree144.table
  base := (-933026646611042010451384330620613559717/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-626141276187985257525858714430000000000000)
      constant := (12413367037187594099214753204757949677869335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (341281774654368092641/100000000000000000000)
  centralHi := (170640887327184046321/50000000000000000000)
  directionLo := (342472988658906935857/100000000000000000000)
  directionHi := (171236494329453467929/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree145.table
  base := (-2278512888364806281825905582483960340627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-12290315091511361469608920746800000000000000)
      constant := (239068358320224317540580786735256437732371080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree145.table
  base := (-2278512961855471146594695318162502650211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-630570046326048946686015924750000000000000)
      constant := (12598194484276039534296472887320074740279322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342472988658906935857/100000000000000000000)
  centralHi := (171236494329453467929/50000000000000000000)
  directionLo := (859150184087060219/250000000000000000)
  directionHi := (343660073634824087601/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree146.table
  base := (-2223564939169059778315847285733404003053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-12376676109203603408231986348040000000000000)
      constant := (242611815789318993652588341627954528154016120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree146.table
  base := (-889426001929420822939905741125425090283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-634998816464112635846173135070000000000000)
      constant := (12784374935892333545404217416184270852880665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (859150184087060219/250000000000000000)
  centralHi := (343660073634824087601/100000000000000000000)
  directionLo := (344843072223325416257/100000000000000000000)
  directionHi := (172421536111662708129/50000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree147.table
  base := (-4335445404709950966712755848239393568023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-254347696467262149935817386720000000000000)
      constant := (5024103750494224940615662313052212128639540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree147.table
  base := (-867089104402460061867756192456345937623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-13049542583717884183802660110000000000000)
      constant := (264732824296126418320468693497718270311885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344843072223325416257/100000000000000000000)
  centralHi := (172421536111662708129/50000000000000000000)
  directionLo := (173011013168346124591/50000000000000000000)
  directionHi := (346022026336692249183/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree148.table
  base := (-844394477324755149973616142788094911773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-12549398144588087285478117550520000000000000)
      constant := (249776162244755307276464497865786334932312300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree148.table
  base := (-84439449828176156364987587789809871857/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-643856356740240014166487555710000000000000)
      constant := (13160794846630110821076749215754965813950350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173011013168346124591/50000000000000000000)
  centralHi := (346022026336692249183/100000000000000000000)
  directionLo := (347196977175607708059/100000000000000000000)
  directionHi := (17359848858780385403/5000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree149.table
  base := (-2053355427154965382317473274953909490833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-12635759162280329224101183151760000000000000)
      constant := (253397051171308119090112943372927337397967320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree149.table
  base := (-2053355473954586688196208850593510350351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-648285126878303703326644766030000000000000)
      constant := (13351034302778527725512473527301835985665602) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (347196977175607708059/100000000000000000000)
  centralHi := (17359848858780385403/5000000000000000000)
  directionLo := (174183982622978550849/50000000000000000000)
  directionHi := (348367965245957101699/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree150.table
  base := (-1994830418734018071720859715119453798559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-12722120179972571162724248753000000000000000)
      constant := (257043750524769829801332991108365870554824360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree150.table
  base := (-3989660921071876469588519052038597881519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-652713897016367392486801976350000000000000)
      constant := (13542626757507079716204928381450108703805569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174183982622978550849/50000000000000000000)
  centralHi := (348367965245957101699/100000000000000000000)
  directionLo := (8738375759378043961/2500000000000000000)
  directionHi := (349535030375121758441/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree151.table
  base := (-3870822365283553499025402626141042231541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-12808481197664813101347314354240000000000000)
      constant := (260716260276538687029642377866318778613089820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree151.table
  base := (-483852804994517365631816901169932018917/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-657142667154431081646959186670000000000000)
      constant := (13735572209391864923620488041601386648584536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8738375759378043961/2500000000000000000)
  centralHi := (349535030375121758441/100000000000000000000)
  directionLo := (350698211727784841851/100000000000000000000)
  directionHi := (87674552931946210463/25000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree152.table
  base := (-3750195466443380934981492937880793299837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-12894842215357055039970379955480000000000000)
      constant := (264414580398501530633517516782524822566159740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree152.table
  base := (-468774441641994245958085758393701600903/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-661571437292494770807116396990000000000000)
      constant := (13929870657032757679740315732949668972446024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (350698211727784841851/100000000000000000000)
  centralHi := (87674552931946210463/25000000000000000000)
  directionLo := (175928773910633448189/50000000000000000000)
  directionHi := (351857547821266896379/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree153.table
  base := (-725556033830113821205702845094830587767/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-12981203233049296978593445556720000000000000)
      constant := (268138710863019370971334254474168330119941700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree153.table
  base := (-1813890114356700013137830939316944790669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-666000207430558459967273607310000000000000)
      constant := (14125522099052756141550433633086939410514438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (175928773910633448189/50000000000000000000)
  centralHi := (351857547821266896379/100000000000000000000)
  directionLo := (176506538270204056007/50000000000000000000)
  directionHi := (70602615308081622403/20000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree154.table
  base := (-1751788250569116953442984757671503030401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-266684984709010998310541044040000000000000)
      constant := (5548747992712525601352397509701139878783960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree154.table
  base := (-3503576554331297861455509999851784506769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-13682224032012696920967975870000000000000)
      constant := (292296459879538001873122600440148215493231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176506538270204056007/50000000000000000000)
  centralHi := (70602615308081622403/20000000000000000000)
  directionLo := (11067651098500424261/3125000000000000000)
  directionHi := (354164835152013576353/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree155.table
  base := (-3377584489682733642209438244317350544251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-13153925268433780855839576759200000000000000)
      constant := (275664402711453849979754719437993996466634020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree155.table
  base := (-135103381487410544547051651203253224699/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-674857747706685838287588027950000000000000)
      constant := (14520883960833990339554906116776014799743725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11067651098500424261/3125000000000000000)
  centralHi := (354164835152013576353/100000000000000000000)
  directionLo := (177656430159438548441/50000000000000000000)
  directionHi := (355312860318877096883/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree156.table
  base := (-1624902080808085819918289267986249844401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-13240286286126022794462642360440000000000000)
      constant := (279465964042344196250515073900978950304974040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree156.table
  base := (-81245105100880126391484040739573766277/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-679286517844749527447745238270000000000000)
      constant := (14720594377951405404002783279110435418097080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177656430159438548441/50000000000000000000)
  centralHi := (355312860318877096883/100000000000000000000)
  directionLo := (356457188113398523921/100000000000000000000)
  directionHi := (178228594056699261961/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree157.table
  base := (-156011777166913956177689664963909871087/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-13326647303818264733085707961680000000000000)
      constant := (283293335609713056679237866513520366526694800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree157.table
  base := (-312023558121630360012503372262527919403/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-683715287982813216607902448590000000000000)
      constant := (14921657784159183395903343587531361319492530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356457188113398523921/100000000000000000000)
  centralHi := (178228594056699261961/50000000000000000000)
  directionLo := (89399463507702220859/25000000000000000000)
  directionHi := (357597854030808883437/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree158.table
  base := (-149443933041386383881320031221968781249/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-13413008321510506671708773562920000000000000)
      constant := (287146517388101333113343085547217411887519600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree158.table
  base := (-373609836831190049869927602440656420723/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-688144058120876905768059658910000000000000)
      constant := (15124074178187197218814167492283262683076584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89399463507702220859/25000000000000000000)
  centralHi := (357597854030808883437/100000000000000000000)
  directionLo := (358734893002017037511/100000000000000000000)
  directionHi := (44841861625252129689/12500000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree159.table
  base := (-1427866769826457870278397457077231454081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-13499369339202748610331839164160000000000000)
      constant := (291025509352451995083098384487425626350001240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree159.table
  base := (-1427866784925830556790667530738038394491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-692572828258940594928216869230000000000000)
      constant := (15327843558785123395325733198447672237339882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (358734893002017037511/100000000000000000000)
  centralHi := (44841861625252129689/12500000000000000000)
  directionLo := (359868339406091026773/100000000000000000000)
  directionHi := (179934169703045513387/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree160.table
  base := (-2720800204982269195094487334866817476291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-13585730356894990548954904765400000000000000)
      constant := (294930311478099985223409242391030518873234820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree160.table
  base := (-1360400115972515293723459037258995959967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-697001598397004284088374079550000000000000)
      constant := (15532965924721968988108689766348618395923234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359868339406091026773/100000000000000000000)
  centralHi := (179934169703045513387/50000000000000000000)
  directionLo := (360998227082386712113/100000000000000000000)
  directionHi := (180499113541193356057/50000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree161.table
  base := (-161504917599630763618246452971726416341/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-279022272950759846685264701360000000000000)
      constant := (6099202525321685009003188636822047546770880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree161.table
  base := (-516815741133341132908199007486810643279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-14314905480307509658133291630000000000000)
      constant := (321213087240522800649138382902565946783605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360998227082386712113/100000000000000000000)
  centralHi := (180499113541193356057/50000000000000000000)
  directionLo := (181062294671167910639/50000000000000000000)
  directionHi := (362124589342335821279/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree162.table
  base := (-1222784496943000532002578164321090316541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-13758452392279474426201035967880000000000000)
      constant := (302817346116530071806384513124258662979579640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree162.table
  base := (-244556901537745173169884130462908700773/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-705859138673131662408688500190000000000000)
      constant := (15947269607782390622468077693713174736621230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181062294671167910639/50000000000000000000)
  centralHi := (362124589342335821279/100000000000000000000)
  directionLo := (363247458980905017901/100000000000000000000)
  directionHi := (181623729490452508951/50000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree163.table
  base := (-1152635582941985171619298533055409806063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-13844813409971716364824101569120000000000000)
      constant := (306799578581857049201485671072764396780116520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree163.table
  base := (-2305271185070306181865449389331686337909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-710287908811195351568845710510000000000000)
      constant := (16156450922536630327835275927662747369442459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363247458980905017901/100000000000000000000)
  centralHi := (181623729490452508951/50000000000000000000)
  directionLo := (364366868287737145097/100000000000000000000)
  directionHi := (182183434143868572549/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree164.table
  base := (-216318522125101855656589607946797769939/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-13931174427663958303447167170360000000000000)
      constant := (310807621113553739495505559042673381854597800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree164.table
  base := (-270398154797356233502573415072796628511/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-714716678949259040729002920830000000000000)
      constant := (16366985217890290886113366830651463721623688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (364366868287737145097/100000000000000000000)
  centralHi := (182183434143868572549/50000000000000000000)
  directionLo := (182741424528992675851/50000000000000000000)
  directionHi := (365482849057985351703/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree165.table
  base := (-1009655591647778582751024998853554766139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-14017535445356200242070232771600000000000000)
      constant := (314841473688777899456159480337572032658367560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree165.table
  base := (-2019311198585185715238077665723738347149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-719145449087322729889160131150000000000000)
      constant := (16578872492702549253973733096879536820989699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182741424528992675851/50000000000000000000)
  centralHi := (365482849057985351703/100000000000000000000)
  directionLo := (14663817304114015419/4000000000000000000)
  directionHi := (91648858150712596369/25000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree166.table
  base := (-1873649074979425233312209881915532973701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-14103896463048442180693298372840000000000000)
      constant := (318901136285026926801447586917594777685773020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree166.table
  base := (-936824544313820978075613565654481795223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-723574219225386419049317341470000000000000)
      constant := (16792112745849427348017342697725860784068146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14663817304114015419/4000000000000000000)
  centralHi := (91648858150712596369/25000000000000000000)
  directionLo := (367704649759830933011/100000000000000000000)
  directionHi := (91926162439957733253/25000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree167.table
  base := (-863099459462814837938375569392380012971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-14190257480740684119316363974080000000000000)
      constant := (322986608880130274753807110884183935174576840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree167.table
  base := (-1726198931108215930807449404444433009097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-728002989363450108209474551790000000000000)
      constant := (17006705976223427298581872362522222782554247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367704649759830933011/100000000000000000000)
  centralHi := (91926162439957733253/25000000000000000000)
  directionLo := (368810530902696499847/100000000000000000000)
  directionHi := (46101316362837062481/12500000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree168.table
  base := (-1576960737425809366462560663513142721707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000000
      center := (303)
      previous := (117)
      next := (0)
      square := (3163407241474063685826578800000000000000)
      linear := (-291359561192508695059988358680000000000000)
      constant := (6675467172494737494233398022041737145565860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree168.table
  base := (-1576960748299773025730136373669108729913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (6)
      next := (0)
      square := (158170362073703184291328940000000000000)
      linear := (-14947586928602322395298607390000000000000)
      constant := (351482697606799565341381140586330891270087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell004.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (368810530902696499847/100000000000000000000)
  centralHi := (46101316362837062481/12500000000000000000)
  directionLo := (92478276487797988819/25000000000000000000)
  directionHi := (369913105951191955277/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree169.table
  base := (-71296727622371986504881010985616058311/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9800000000000000000000000000000000000000000
      center := (14847)
      previous := (5733)
      next := (0)
      square := (155006954832229120605502361200000000000000)
      linear := (-14362979516125167996562495176560000000000000)
      constant := (331234983979834388275808341376838925257104400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree169.table
  base := (-1425934562153014101558348849082453554321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (735)
      previous := (294)
      next := (0)
      square := (7750347741611456030275118060000000000000)
      linear := (-736860529639577486529788972430000000000000)
      constant := (17439951364303097215283439296654959775838271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell004.Kernel169
