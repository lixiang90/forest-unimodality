import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell033.Parameters
import ForestUnimodality.BinomialMassData.Q1687_3572.Batch000_049
import ForestUnimodality.BinomialMassData.Q1687_3572.Batch050_099
import ForestUnimodality.BinomialMassData.Q1687_3572.Batch100_149
import ForestUnimodality.BinomialMassData.Q1687_3572.Batch150_199
import ForestUnimodality.BinomialMassData.Q9_19.Batch000_049
import ForestUnimodality.BinomialMassData.Q9_19.Batch050_099
import ForestUnimodality.BinomialMassData.Q9_19.Batch100_149
import ForestUnimodality.BinomialMassData.Q9_19.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree000.table
  base := (77935043447091387692751141/1000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (347267884901236445482908265000000000000)
      linear := (22435120706248046391906303500000000000)
      constant := (389675217235456938463755705000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree000.table
  base := (77935043447091387692751141/1000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (347267884901236445482908265000000000000)
      linear := (22435120706248046391906303500000000000)
      constant := (389675217235456938463755705000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree001.table
  base := (56631841652435807421059753283301858954107/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-243687107024297498648816687704286000000000000)
      constant := (180697342000911440123647128638798743421874692172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree001.table
  base := (452090233410107729397828841366358880591423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-221333076122534639215352902133000000000000)
      constant := (163253158847121353784918410916388555893503703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49923125646186015803/100000000000000000000)
  directionHi := (12480781411546503951/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree002.table
  base := (5466713921647265143589177507530922441827/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-505265078620671795644812665228343500000000000)
      constant := (109215818007659432120801292433551101257812483075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree002.table
  base := (136138367267886272547829978674372247521863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-229432154697490183962831077696500000000000)
      constant := (49250792567133408166237052623511381355392543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49923125646186015803/100000000000000000000)
  centralHi := (12480781411546503951/25000000000000000000)
  directionLo := (70601961364892348123/100000000000000000000)
  directionHi := (17650490341223087031/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree003.table
  base := (21603727050972576517159821192257394060033/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-766843050217046092640808642752401000000000000)
      constant := (69442059821470737369239519670997356730617023268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree003.table
  base := (5373302689157664073090409361856537494907/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-348197771333713048317985704326500000000000)
      constant := (31277845403745363807128196665572860570582832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70601961364892348123/100000000000000000000)
  centralHi := (17650490341223087031/25000000000000000000)
  directionLo := (86469390091839017747/100000000000000000000)
  directionHi := (21617347522959754437/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree004.table
  base := (115340322106659694088913161460609971267911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-2056842043626840779273609240552917000000000000)
      constant := (93887055179026887711224826959537493977624359039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree004.table
  base := (14333839318284960655970156103773033691781/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-466963387969935912673140330956500000000000)
      constant := (21132777531872411956834690613694260650931764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86469390091839017747/100000000000000000000)
  centralHi := (21617347522959754437/25000000000000000000)
  directionLo := (99846251292372031607/100000000000000000000)
  directionHi := (12480781411546503951/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree005.table
  base := (81399176097148179553515506664344893027243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-2579997986819589373265601195601032000000000000)
      constant := (67915675920689049652361873201415702474681903107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree005.table
  base := (40454944301538398218531719783163462955227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-585729004606158777028294957586500000000000)
      constant := (15288270331576523479327760188854510126836947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99846251292372031607/100000000000000000000)
  centralHi := (12480781411546503951/12500000000000000000)
  directionLo := (55815751297067522967/50000000000000000000)
  directionHi := (22326300518827009187/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree006.table
  base := (12096479555526813571128312738981480249371/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-3103153930012337967257593150649147000000000000)
      constant := (52577644061153072235258002653894189216903272895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree006.table
  base := (12025151339199637935224299021262540124803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-1408989242484763282766899168433000000000000)
      constant := (23684627604310136431939989000076884925269415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55815751297067522967/50000000000000000000)
  centralHi := (22326300518827009187/20000000000000000000)
  directionLo := (24457236839601693147/20000000000000000000)
  directionHi := (15285773024751058217/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree007.table
  base := (9379545179984471210774991153015914523467/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-3626309873205086561249585105697262000000000000)
      constant := (43333671560307098559283667064382808479121178415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree007.table
  base := (46632701703595676675815533163455053879859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-1646520475757209011477208421693000000000000)
      constant := (19537308106373296361150509588998274450629099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24457236839601693147/20000000000000000000)
  centralHi := (15285773024751058217/12500000000000000000)
  directionLo := (33021043782709734407/25000000000000000000)
  directionHi := (132084175130838937629/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree008.table
  base := (18772271967324329601373728530393212628687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-2074732908198917577620788530372688500000000000)
      constant := (18855587433713014607030087612836640017533819463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree008.table
  base := (4667625000602376137650695348320553201683/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-942025854514827370093758837476500000000000)
      constant := (8509595971071693548686872705546878823230252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33021043782709734407/25000000000000000000)
  centralHi := (132084175130838937629/100000000000000000000)
  directionLo := (141203922729784696247/100000000000000000000)
  directionHi := (17650490341223087031/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree009.table
  base := (15359221307895233414067156047626140428851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-2336310879795291874616784507896746000000000000)
      constant := (17175487258864739622253607499795912996346801099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree009.table
  base := (6111187917368828806884630165817553573931/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-2121582942302100468897826928213000000000000)
      constant := (15518488074990929147259192100457684200945455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141203922729784696247/100000000000000000000)
  centralHi := (17650490341223087031/12500000000000000000)
  directionLo := (149769376938558047411/100000000000000000000)
  directionHi := (37442344234639511853/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree010.table
  base := (25469835980335206094977277989136289035507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-5195777702783332343225560970841607000000000000)
      constant := (32495824134599035455880425660250964555076021643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree010.table
  base := (2533514884301415413964605282415164155041/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-1179557087787273098804068090736500000000000)
      constant := (7347500177456385871287509702274371299849005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149769376938558047411/100000000000000000000)
  centralHi := (37442344234639511853/25000000000000000000)
  directionLo := (9866924059794570283/6250000000000000000)
  directionHi := (157870784956713124529/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree011.table
  base := (10629547249008496095537315450953646665659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-2859466822988040468608776462944861000000000000)
      constant := (15857698344376849135287177366371482767383103891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree011.table
  base := (10571954232069211765758921365951572036419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-1298322704423495963159222717366500000000000)
      constant := (7177847555645551274353778761490017505147259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9866924059794570283/6250000000000000000)
  centralHi := (157870784956713124529/100000000000000000000)
  directionLo := (646782328633468673/390625000000000000)
  directionHi := (165576276130167980289/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree012.table
  base := (4442709405692849954896694970081366343549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-3121044794584414765604772440468918500000000000)
      constant := (15879096139557468900024783625498840518593613002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree012.table
  base := (1767000189158924121492743637831639897653/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-1417088321059718827514377343996500000000000)
      constant := (7193931083230658948210852534464110015263665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (646782328633468673/390625000000000000)
  centralHi := (165576276130167980289/100000000000000000000)
  directionLo := (86469390091839017747/50000000000000000000)
  directionHi := (34587756036735607099/20000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree013.table
  base := (14813692361477311865861172241007867556929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-6765245532361578125201536835985952000000000000)
      constant := (32471600703691312322343499730204070850405474121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree013.table
  base := (2944803625500165644221592784674642408971/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-3071707875391883383739063941253000000000000)
      constant := (14723124150193871577992622030146729548192655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86469390091839017747/50000000000000000000)
  centralHi := (34587756036735607099/20000000000000000000)
  directionLo := (180000389348754983947/100000000000000000000)
  directionHi := (45000097337188745987/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree014.table
  base := (383311983705993915564144933570901708627/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-3644200737777163359596764395517033500000000000)
      constant := (16879296083787176704317126555781713446286280368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree014.table
  base := (12185463259873121112876662051410314069883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-3309239108664329112449373194513000000000000)
      constant := (15317982760256740692597330849681123379227763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180000389348754983947/100000000000000000000)
  centralHi := (45000097337188745987/25000000000000000000)
  directionLo := (186795231844895501797/100000000000000000000)
  directionHi := (93397615922447750899/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree015.table
  base := (10046140147995305103594834964054018196921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-7811557418747075313185520746082182000000000000)
      constant := (35554118097045832084725810680204977132116454529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree015.table
  base := (9973461011505008122308732257556206041033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-3546770341936774841159682447773000000000000)
      constant := (16143241660580323892014979267272790380812913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186795231844895501797/100000000000000000000)
  centralHi := (93397615922447750899/50000000000000000000)
  directionLo := (96675717109149413423/50000000000000000000)
  directionHi := (193351434218298826847/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree016.table
  base := (8096428801870179028749820232073799297633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-8334713361939823907177512701130297000000000000)
      constant := (37812138916183145327507103306799991176098138217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree016.table
  base := (1606135700417366143470789319243456062729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-3784301575209220569869991701033000000000000)
      constant := (17178203681372834446175434994562438193225845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96675717109149413423/50000000000000000000)
  centralHi := (193351434218298826847/100000000000000000000)
  directionLo := (39938500516948812643/20000000000000000000)
  directionHi := (12480781411546503951/6250000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree017.table
  base := (6373892412961759891096547955277136697531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-8857869305132572501169504656178412000000000000)
      constant := (40498398586559086047023650500547123257309398419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree017.table
  base := (6314387022243942401950224849117964626167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-4021832808481666298580300954293000000000000)
      constant := (18407443758550024970000287072752585230046287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39938500516948812643/20000000000000000000)
  centralHi := (12480781411546503951/6250000000000000000)
  directionLo := (25729790025025858349/12500000000000000000)
  directionHi := (205838320200206866793/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree018.table
  base := (484520468539293364432735870350099489833/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-4690512624162660547580748305613263500000000000)
      constant := (21793160543426372762080727778261145440339180085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree018.table
  base := (18716368519418313255004900614186524021/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-2129682020877056013645305103776500000000000)
      constant := (9909489026359499207346423352067330901962368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25729790025025858349/12500000000000000000)
  centralHi := (205838320200206866793/100000000000000000000)
  directionLo := (211805884094677044371/100000000000000000000)
  directionHi := (52951471023669261093/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree019.table
  base := (3483666000742965324200184459689336688091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (344604)
      previous := (172302)
      next := (172302)
      square := (1534229515493662616143488714770000000000000)
      linear := (-27435404962653932656934871374722000000000000)
      constant := (130345193443363232915292647026571119743993019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree019.table
  base := (214691540170732175452135197562738678551/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (347267884901236445482908265000000000000)
      linear := (-6228386807516007972300442466500000000000)
      constant := (29644314912009777070205494314001909428408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211805884094677044371/100000000000000000000)
  centralHi := (52951471023669261093/25000000000000000000)
  directionLo := (217609859637408529951/100000000000000000000)
  directionHi := (6800308113669016561/3125000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree020.table
  base := (283422953565445148529211071514308325187/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-5213668567355409141572740260661378500000000000)
      constant := (25442910744564035682576610564586587138448191852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree020.table
  base := (2223564159821140116198407191425096957309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-4734426508299003484711228714073000000000000)
      constant := (23152209377664816611919441452164460001588549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217609859637408529951/100000000000000000000)
  centralHi := (6800308113669016561/3125000000000000000)
  directionLo := (223263005188270091869/100000000000000000000)
  directionHi := (22326300518827009187/10000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree021.table
  base := (589058633701032655827583430730666344831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-5475246538951783438568736238185436000000000000)
      constant := (27532697672508576618902557019587341083519136119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree021.table
  base := (569340488932756492400260791310442740543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-2485978870785724606710768983666500000000000)
      constant := (12529723514605655428258124743859569829336023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223263005188270091869/100000000000000000000)
  centralHi := (22326300518827009187/10000000000000000000)
  directionLo := (57194125550609650143/25000000000000000000)
  directionHi := (228776502202438600573/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree022.table
  base := (200507086881310822686929583293215366083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-11473649021096315471129464431418987000000000000)
      constant := (59581087719251237475644077397585380300467522267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree022.table
  base := (10317549488875717568371808940432784919/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-2604744487421947471065923610296500000000000)
      constant := (13559686318495041530523041891512969882846072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57194125550609650143/25000000000000000000)
  centralHi := (228776502202438600573/100000000000000000000)
  directionLo := (46832043062103224777/20000000000000000000)
  directionHi := (117080107655258061943/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree023.table
  base := (-678471205947287146790322828091872899473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-11996804964289064065121456386467102000000000000)
      constant := (64422512402474665984173243885035784423188155623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree023.table
  base := (-710238067119208841250441960541163011617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-5447020208116340670842156473853000000000000)
      constant := (29327292598560779380384127962883640152806263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46832043062103224777/20000000000000000000)
  centralHi := (117080107655258061943/50000000000000000000)
  directionLo := (239422899716280576281/100000000000000000000)
  directionHi := (119711449858140288141/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree024.table
  base := (-146991085278345015998735760779240777499/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-6259980453740906329556724170757608500000000000)
      constant := (34790411550093618751265875190331925106120999745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree024.table
  base := (-1498347250462669856848685062312718516557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-5684551441388786399552465727113000000000000)
      constant := (31679210047730267417793993777057108615522923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239422899716280576281/100000000000000000000)
  centralHi := (119711449858140288141/50000000000000000000)
  directionLo := (24457236839601693147/10000000000000000000)
  directionHi := (244572368396016931471/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree025.table
  base := (-1091643610974296578367162332179206152799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-6521558425337280626552720148281666000000000000)
      constant := (37524231844698204004183491835023135170156590249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree025.table
  base := (-1104350413692819657405023680752506118873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-2961041337330616064131387490186500000000000)
      constant := (17085856032762776757923617919410845291086847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24457236839601693147/10000000000000000000)
  centralHi := (244572368396016931471/100000000000000000000)
  directionLo := (249615628230930079019/100000000000000000000)
  directionHi := (12480781411546503951/5000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree026.table
  base := (-2826708330379617260446761947826150381751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-13566272793867309847097432251611447000000000000)
      constant := (80818968440103862637712346430464576204223046801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree026.table
  base := (-113975425443061762620128651145050675689/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-6159613907933677856973084233633000000000000)
      constant := (36801879303360615581560757989373917651906775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249615628230930079019/100000000000000000000)
  centralHi := (12480781411546503951/5000000000000000000)
  directionLo := (127279495924723450081/50000000000000000000)
  directionHi := (254558991849446900163/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree027.table
  base := (-1703560018063431465865708593836774738649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-7044714368530029220544712103329781000000000000)
      constant := (43443399192376607720298724145897162008939093599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree027.table
  base := (-1713663285174020105454157481969063343439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-3198572570603061792841696743446500000000000)
      constant := (19783605937284542381059867885734668133018521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127279495924723450081/50000000000000000000)
  centralHi := (254558991849446900163/100000000000000000000)
  directionLo := (129704085137758526621/50000000000000000000)
  directionHi := (259408170275517053243/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree028.table
  base := (-3930476867201340820536969661937088876317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-14612584680252807035081416161707677000000000000)
      constant := (93247205090936613985231364912444601412669884667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree028.table
  base := (-3948457601922187628713621420678784037917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-6634676374478569314393702740153000000000000)
      constant := (42465567615359297441678700825938958962311963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129704085137758526621/50000000000000000000)
  centralHi := (259408170275517053243/100000000000000000000)
  directionLo := (33021043782709734407/12500000000000000000)
  directionHi := (264168350261677875257/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree029.table
  base := (-220094289964656014484767980048307899107/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-7567870311722777814536704058377896000000000000)
      constant := (49948058002998494074146564193831759079150219570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree029.table
  base := (-4417865766276468670111779205160862252271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-6872207607751015043104011993413000000000000)
      constant := (45495110105923882491457108828953928726930169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33021043782709734407/12500000000000000000)
  centralHi := (264168350261677875257/100000000000000000000)
  directionLo := (134422129645997463867/50000000000000000000)
  directionHi := (53768851858398985547/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree030.table
  base := (-1206432032449474157654633629377921521053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-7829448283319152111532700035901953500000000000)
      constant := (53415018634353719057670786292677679221915612406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree030.table
  base := (-4839913219862524008833810764708569975983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-7109738841023460771814321246673000000000000)
      constant := (48654264607783797628238060677030206238670137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134422129645997463867/50000000000000000000)
  centralHi := (53768851858398985547/20000000000000000000)
  directionLo := (6836005514395188307/2500000000000000000)
  directionHi := (273440220575807532281/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree031.table
  base := (-5205763259039375363844329050264098224411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-16182052509831052817057392026852022000000000000)
      constant := (114045970949039225242729321810731081510041672461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree031.table
  base := (-5218341164300485503397292388375756860067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-7347270074295906500524630499933000000000000)
      constant := (51941680547154175251096711329819351773515813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6836005514395188307/2500000000000000000)
  centralHi := (273440220575807532281/100000000000000000000)
  directionLo := (138980099926960004361/50000000000000000000)
  directionHi := (277960199853920008723/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree032.table
  base := (-5545217322952417373677750107837751688677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-16705208453023801411049383981900137000000000000)
      constant := (121541344368117230653128232609523076753616215027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree032.table
  base := (-5556358579122666168964048221498922503481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-7584801307568352229234939753193000000000000)
      constant := (55356199482423850361559642270854888976243359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138980099926960004361/50000000000000000000)
  centralHi := (277960199853920008723/100000000000000000000)
  directionLo := (56481569091913878499/20000000000000000000)
  directionHi := (17650490341223087031/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree033.table
  base := (-5846859028548021366815404778468033933221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-17228364396216550005041375936948252000000000000)
      constant := (129313949623304240438881802355825122682986846771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree033.table
  base := (-732089764717150371270443315604028738097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-3911166270420398978972624503226500000000000)
      constant := (29448413852856242757697807729002282502187932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56481569091913878499/20000000000000000000)
  centralHi := (17650490341223087031/6250000000000000000)
  directionLo := (286786522785504871141/100000000000000000000)
  directionHi := (143393261392752435571/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree034.table
  base := (-1528266153930370196130824798574806705563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-8875760169704649299516683945998183500000000000)
      constant := (68680945892235996370272947862782446934910982426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree034.table
  base := (-3060890547999201257950922927006349349341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-4029931887056621843327779129856500000000000)
      constant := (31281356390998338013394771876341707884887899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286786522785504871141/100000000000000000000)
  centralHi := (143393261392752435571/50000000000000000000)
  directionLo := (36387418010403545543/12500000000000000000)
  directionHi := (58219868816645672869/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree035.table
  base := (-634587354549033536071053802428911283059/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-9137338141301023596512679923522241000000000000)
      constant := (72841772242735755757427215554793337818679417545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree035.table
  base := (-3176786589951759537157267674486264721387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-4148697503692844707682933756486500000000000)
      constant := (33176561722925706552472239737687958435579293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36387418010403545543/12500000000000000000)
  centralHi := (58219868816645672869/20000000000000000000)
  directionLo := (73837298586135760841/25000000000000000000)
  directionHi := (59069838868908608673/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree036.table
  base := (-654703626061354262909452944385320813283/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-9398916112897397893508675901046298500000000000)
      constant := (77138755918737554417750997537906770013841424665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree036.table
  base := (-3276916062244076192493942970145638612159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-4267463120329067572038088383116500000000000)
      constant := (35133716183854422621934889410071424461010601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73837298586135760841/25000000000000000000)
  centralHi := (59069838868908608673/20000000000000000000)
  directionLo := (299538753877116094823/100000000000000000000)
  directionHi := (37442344234639511853/12500000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree037.table
  base := (-671805515907053595919626699678376979319/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-9660494084493772190504671878570356000000000000)
      constant := (81571297877358241770698720421870947718595213845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree037.table
  base := (-1344809741961216486856167239201432052651/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-8772457473930580872786486019493000000000000)
      constant := (74305101375969557868489864963922415144964945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299538753877116094823/100000000000000000000)
  centralHi := (37442344234639511853/12500000000000000000)
  directionLo := (151835259037995196673/50000000000000000000)
  directionHi := (303670518075990393347/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree038.table
  base := (-3430109875666445253743748426762019052623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (172302)
      previous := (86151)
      next := (86151)
      square := (767114757746831308071744357385000000000000)
      linear := (-27484964144294034591414592399153500000000000)
      constant := (238611866922935718137932868284623199912755793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree038.table
  base := (-6865501849493722572268509974673828659597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (156)
      previous := (78)
      next := (78)
      square := (694535769802472890965816530000000000000)
      linear := (-24958417471476527981985582473000000000000)
      constant := (217356423221082564430547418819326171340403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151835259037995196673/50000000000000000000)
  centralHi := (303670518075990393347/100000000000000000000)
  directionLo := (38468351850666088349/12500000000000000000)
  directionHi := (307746814805328706793/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree039.table
  base := (-6974636830507601436289616773372290461029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-20367300055373041568993327667236942000000000000)
      constant := (181682145717348043512874228927327052719142884979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree039.table
  base := (-6979288704738717904280668253292398989579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-9247519940475472330207104526013000000000000)
      constant := (82748738513043849033658994797008443964761981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38468351850666088349/12500000000000000000)
  centralHi := (307746814805328706793/100000000000000000000)
  directionLo := (155884909867111704359/50000000000000000000)
  directionHi := (311769819734223408719/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree040.table
  base := (-3531128182326431859039161823275693669741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-10445227999282895081492659811142528500000000000)
      constant := (95677485800301904535325881455908936358758709291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree040.table
  base := (-883293814492970455367077914631639229061/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-4742525586873959029458706889636500000000000)
      constant := (43576985389441657359714211519331912953235916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155884909867111704359/50000000000000000000)
  centralHi := (311769819734223408719/100000000000000000000)
  directionLo := (315741569913426249057/100000000000000000000)
  directionHi := (157870784956713124529/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree041.table
  base := (-111310839356642349389466429406601343397/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-10706805970879269378488655788666586000000000000)
      constant := (100647797678038998861532968958379172227400983904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree041.table
  base := (-7127494761984497464607430914800356227587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-9722582407020363787627723032533000000000000)
      constant := (91681074080455097615565951793410071401841093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315741569913426249057/100000000000000000000)
  centralHi := (157870784956713124529/50000000000000000000)
  directionLo := (63932795166699824753/20000000000000000000)
  directionHi := (159831987916749561883/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree042.table
  base := (-7160248727663285954741875591173747799731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-21936767884951287350969303532381287000000000000)
      constant := (211503458901337617745837873274757289990852313781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree042.table
  base := (-7163414169660649002931098473120911048983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-9960113640292809516338032285793000000000000)
      constant := (96329798343384495324328260380249351111317137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63932795166699824753/20000000000000000000)
  centralHi := (159831987916749561883/50000000000000000000)
  directionLo := (64707766433393383731/20000000000000000000)
  directionHi := (631911781576107263/195312500000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree043.table
  base := (-1792980516291119271373845538316737684603/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-11229961914072017972480647743714701000000000000)
      constant := (110989041614752183219036593463074291887802044506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree043.table
  base := (-717470302133709570692725382851727486343/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-5098822436782627622524170769526500000000000)
      constant := (50549964515868893543309631575102131887150885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64707766433393383731/20000000000000000000)
  centralHi := (631911781576107263/195312500000000000)
  directionLo := (163683913682934695107/50000000000000000000)
  directionHi := (65473565473173878043/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree044.table
  base := (-7159429294826101901528742923523776460219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-22983079771336784538953287442477517000000000000)
      constant := (232719057204982791194794402857102450985574818669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree044.table
  base := (-7161871144926994849240213797623260061231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-10435176106837700973758650792313000000000000)
      constant := (105991282097638323127014361732470003117895609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163683913682934695107/50000000000000000000)
  centralHi := (65473565473173878043/20000000000000000000)
  directionLo := (331152552260335960577/100000000000000000000)
  directionHi := (165576276130167980289/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree045.table
  base := (-356160646446740501656671284388051846181/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-11753117857264766566472639698762816000000000000)
      constant := (121863013973396207777487610186643530370648077310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree045.table
  base := (-3562677957840757578521849585599847428449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-5336353670055073351234480022786500000000000)
      constant := (55501849824310215767501921460790955078329911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331152552260335960577/100000000000000000000)
  centralHi := (165576276130167980289/50000000000000000000)
  directionLo := (83723626945601284451/25000000000000000000)
  directionHi := (66978901556481027561/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree046.table
  base := (-1765913194785644025304619886805374075533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-12014695828861140863468635676286873500000000000)
      constant := (127499346287255592004573169588982735997680569366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree046.table
  base := (-7065532552379693364328664233974094569463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-10910238573382592431179269298833000000000000)
      constant := (116137046230704880049616972220753351860423857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83723626945601284451/25000000000000000000)
  centralHi := (66978901556481027561/20000000000000000000)
  directionLo := (84648777980364360407/25000000000000000000)
  directionHi := (338595111921457441629/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree047.table
  base := (-6981074840465026924935767443335512517869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-11114779357589420697568702266918000000000000)
      constant := (120659479911154314153916670584136254981049291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree047.table
  base := (-3491361475162930922452396688829194956377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-5573884903327519079944789276046500000000000)
      constant := (60695602819843402341954226782288160620747903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84648777980364360407/25000000000000000000)
  centralHi := (338595111921457441629/100000000000000000000)
  directionLo := (17112785300133725397/5000000000000000000)
  directionHi := (342255706002674507941/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree048.table
  base := (-343787945825690706850469347656161384179/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-12537851772053889457460627631334988500000000000)
      constant := (139170050232684097721338889955882235603478406290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree048.table
  base := (-687720325909971266789848816093370349471/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-5692650519963741944299943902676500000000000)
      constant := (63383039092783968300461827995183466519204845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17112785300133725397/5000000000000000000)
  centralHi := (342255706002674507941/100000000000000000000)
  directionLo := (345877560367356070989/100000000000000000000)
  directionHi := (34587756036735607099/10000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree049.table
  base := (-42174657277014107143001671601885053351/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-12799429743650263754456623608859046000000000000)
      constant := (145204214543205033456312219629631004224723872080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree049.table
  base := (-6749210383445962347504526707035435984763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-11622832273199929617310197058613000000000000)
      constant := (132261578345735433139038264595637207609500557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345877560367356070989/100000000000000000000)
  centralHi := (34587756036735607099/10000000000000000000)
  directionLo := (349461879523302110627/100000000000000000000)
  directionHi := (87365469880825527657/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree050.table
  base := (-6597839711847943946845324416806721332763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-26122015430493276102905239172766207000000000000)
      constant := (302741612610331843779403332423049246879909478413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree050.table
  base := (-659894756033658582879349403714359135219/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-5930181753236187673010253155936500000000000)
      constant := (68938816375821205671540899093870581760929705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349461879523302110627/100000000000000000000)
  centralHi := (87365469880825527657/25000000000000000000)
  directionLo := (353009806824461740619/100000000000000000000)
  directionHi := (17650490341223087031/5000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree051.table
  base := (-1285123895908756455400416865881715007071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-26645171373686024696897231127814322000000000000)
      constant := (315339509952095275228150814997398337621631190605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree051.table
  base := (-6426589143489527730485902399402685749263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-12097894739744821074730815565133000000000000)
      constant := (143614178461596693205696151845098630444516057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353009806824461740619/100000000000000000000)
  centralHi := (17650490341223087031/5000000000000000000)
  directionLo := (71304485746277890339/20000000000000000000)
  directionHi := (22282651795711840731/6250000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree052.table
  base := (-62314363187714227364209473325660401939/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-13584163658439386645444611541431218500000000000)
      constant := (164101000008991932173549499731147696406707319450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree052.table
  base := (-155807117699261452060519268163906337471/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-6167712986508633401720562409196500000000000)
      constant := (74735580739499785923054719866494596243459380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71304485746277890339/20000000000000000000)
  centralHi := (22282651795711840731/6250000000000000000)
  directionLo := (72000155739501993579/20000000000000000000)
  directionHi := (45000097337188745987/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree053.table
  base := (-3007710281925928865043864682678368927017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-13845741630035760942440607518955276000000000000)
      constant := (170664489436511835031942175941469451315019220367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree053.table
  base := (-3008081285749334382761527611759557342133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-6286478603144856266075717035826500000000000)
      constant := (77724267740577191447653876330719299799489987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72000155739501993579/20000000000000000000)
  centralHi := (45000097337188745987/12500000000000000000)
  directionLo := (363445840720592677681/100000000000000000000)
  directionHi := (181722920360296338841/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree054.table
  base := (-1444421020208303564370390373513316401721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-14107319601632135239436603496479333500000000000)
      constant := (177360178654873239775449619334830425197527980542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree054.table
  base := (-5778332815347494025596663016036501758847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-12810488439562158260861743324913000000000000)
      constant := (161546260728721452690555880158052822865056233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363445840720592677681/100000000000000000000)
  centralHi := (181722920360296338841/50000000000000000000)
  directionLo := (73371710518805079441/20000000000000000000)
  directionHi := (183429276297012698603/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree055.table
  base := (-1103664576856865565330367837512473537763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-28737795146457019072865198948006782000000000000)
      constant := (368376058761430389501085177455177021823922167065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree055.table
  base := (-1379722468987571723066324837295001708391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-6524009836417301994786026289086500000000000)
      constant := (83882151565074170394079832314680508766541698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73371710518805079441/20000000000000000000)
  centralHi := (183429276297012698603/50000000000000000000)
  directionLo := (370239808888331421133/100000000000000000000)
  directionHi := (185119904444165710567/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree056.table
  base := (-2618709691659590887852239129608002436913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-14630475544824883833428595451527448500000000000)
      constant := (191148008755504931507726471890030829064686165063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree056.table
  base := (-1309478692054404881538775287109816509201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-6642775453053524859141180915716500000000000)
      constant := (87051316719526165319066535322630712480356878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370239808888331421133/100000000000000000000)
  centralHi := (185119904444165710567/50000000000000000000)
  directionLo := (74718092737958200719/20000000000000000000)
  directionHi := (93397615922447750899/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree057.table
  base := (-246752215469267854699221931094748424949/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (172302)
      previous := (86151)
      next := (86151)
      square := (767114757746831308071744357385000000000000)
      linear := (-41252225807261102854361749110946000000000000)
      constant := (549141519603549526428850953887462444792876590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree057.table
  base := (-2467738496451038904735782175393754594987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (347267884901236445482908265000000000000)
      linear := (-18730030663960520009685140006500000000000)
      constant := (250084801337481632599722872815106245405013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74718092737958200719/20000000000000000000)
  centralHi := (93397615922447750899/25000000000000000000)
  directionLo := (75382266623984695937/20000000000000000000)
  directionHi := (188455666559961739843/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree058.table
  base := (-144101824090825262104467224409814353517/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-15153631488017632427420587406575563500000000000)
      constant := (205464244638908709751368027000431915257635549872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree058.table
  base := (-4611636172909696114034122161115626017279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-13760613372651941175702980337953000000000000)
      constant := (187140060986107486676533379824131259007762281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75382266623984695937/20000000000000000000)
  centralHi := (188455666559961739843/50000000000000000000)
  directionLo := (190101598828444103439/50000000000000000000)
  directionHi := (380203197656888206879/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree059.table
  base := (-4266113673479460317082498748242131493861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-30830418919228013448833166768199242000000000000)
      constant := (425640912331617525814738936046966212857352039411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree059.table
  base := (-4266443457076646993850316096920845325101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-13998144605924386904413289591213000000000000)
      constant := (193839118235659716164736745112318574837638539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190101598828444103439/50000000000000000000)
  centralHi := (380203197656888206879/100000000000000000000)
  directionLo := (383466804277511977159/100000000000000000000)
  directionHi := (9586670106937799429/2500000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree060.table
  base := (-389965493884587745064275557078068292039/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-15676787431210381021412579361623678500000000000)
      constant := (220308705325927573792349417028029605092908957445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree060.table
  base := (-121873210139252107471643827520843980447/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-7117837919598416316561799422236500000000000)
      constant := (100329191236990122374078876652329605168938128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383466804277511977159/100000000000000000000)
  centralHi := (9586670106937799429/2500000000000000000)
  directionLo := (386702868436597653693/100000000000000000000)
  directionHi := (193351434218298826847/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree061.table
  base := (-1755960275573172773724837942721676166029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-15938365402806755318408575339147736000000000000)
      constant := (227928976814567839547223640124014884000576339979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree061.table
  base := (-702434323492803873441734523328739572239/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-14473207072469278361833908097733000000000000)
      constant := (207597840112156874074597787840304625072108605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386702868436597653693/100000000000000000000)
  centralHi := (193351434218298826847/50000000000000000000)
  directionLo := (194956037949185758079/50000000000000000000)
  directionHi := (389912075898371516159/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree062.table
  base := (-3102943454932033558267294032538280078499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-32399886748806259230809142633343587000000000000)
      constant := (471362514991859735215366446202233500089681050949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree062.table
  base := (-3103162428205009736398837298351736786391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-14710738305741724090544217350993000000000000)
      constant := (214657479492739877132146536522801023020112849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194956037949185758079/50000000000000000000)
  centralHi := (389912075898371516159/100000000000000000000)
  directionLo := (49136885554168708691/12500000000000000000)
  directionHi := (393095084433349669529/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree063.table
  base := (-1336375962968100117354414322227104577057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-16461521345999503912400567294195851000000000000)
      constant := (243565536095786052244620561166745317869630472407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree063.table
  base := (-2672942858841406169295916932659545945817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-14948269539014169819254526604253000000000000)
      constant := (221837290615248639209033551185268903913560063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49136885554168708691/12500000000000000000)
  centralHi := (393095084433349669529/100000000000000000000)
  directionLo := (99063131348129203221/25000000000000000000)
  directionHi := (79250505078503362577/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree064.table
  base := (-444274046526914317515779807814397102637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-33446198635191756418793126543439817000000000000)
      constant := (503163605875401087684481175771376412224496134935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree064.table
  base := (-2221536673906124363180229680786573624271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-15185800772286615547964835857513000000000000)
      constant := (229137264900686777738540636971508046921638169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99063131348129203221/25000000000000000000)
  centralHi := (79250505078503362577/20000000000000000000)
  directionLo := (399385005169488126431/100000000000000000000)
  directionHi := (12480781411546503951/3125000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree065.table
  base := (-218602400508555007480479356706087329069/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-16984677289192252506392559249243966000000000000)
      constant := (259730049716624267591867774956494900399585020076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree065.table
  base := (-349792851982868343437008237183893861983/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-15423332005559061276675145110773000000000000)
      constant := (236557394989522313679580684984328071579120685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399385005169488126431/100000000000000000000)
  centralHi := (12480781411546503951/3125000000000000000)
  directionLo := (402493106560245244371/100000000000000000000)
  directionHi := (100623276640061311093/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree066.table
  base := (-313779179302994966239072153052325761391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-17246255260788626803388555226768023500000000000)
      constant := (268010269304569634367330320227849812747809016882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree066.table
  base := (-313810776361958315143382681948501440379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-7830431619415753502692727182016500000000000)
      constant := (122048837284188613123294843751872181960046362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402493106560245244371/100000000000000000000)
  centralHi := (100623276640061311093/25000000000000000000)
  directionLo := (32446191202326531/8000000000000000)
  directionHi := (405577390029081637501/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree067.table
  base := (-740278115283456907855612745756846062333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-35015666464770002200769102408584162000000000000)
      constant := (552844911167639225409628465742754937239438611483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree067.table
  base := (-370194106506732645727013488912448721137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-7949197236051976367047881808646500000000000)
      constant := (125879049110673268352975268939688106011669543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32446191202326531/8000000000000000)
  centralHi := (405577390029081637501/100000000000000000000)
  directionLo := (51079799361068162439/12500000000000000000)
  directionHi := (408638394888545299513/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree068.table
  base := (-102158283392411440673111062164771639639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-17769411203981375397380547181816138500000000000)
      constant := (284966603303769846166581918970229315520741519089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree068.table
  base := (-12775778273209539739167515155144375951/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-8067962852688199231403036435276500000000000)
      constant := (129769330651223421802738590925293943042253512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51079799361068162439/12500000000000000000)
  centralHi := (408638394888545299513/100000000000000000000)
  directionLo := (82335328080082746717/20000000000000000000)
  directionHi := (205838320200206866793/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree069.table
  base := (70551325266431131981635176344262309353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-36061978351155499388753086318680392000000000000)
      constant := (587285415916110535218016738270031438046656202485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree069.table
  base := (176336568174808663818245630179713237567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-8186728469324422095758191061906500000000000)
      constant := (133719679913095809300734510420363376478761687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82335328080082746717/20000000000000000000)
  centralHi := (205838320200206866793/50000000000000000000)
  directionLo := (82938525360813218877/20000000000000000000)
  directionHi := (207346313402033047193/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree070.table
  base := (465465882082497962948539906119921764127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-18292567147174123991372539136864253500000000000)
      constant := (302450765679087109532888041176286757990881312023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree070.table
  base := (930859082613199013486662261539553689473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-16610988171921289920226691377073000000000000)
      constant := (275460190373717277037579028927625778881899753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82938525360813218877/20000000000000000000)
  centralHi := (207346313402033047193/50000000000000000000)
  directionLo := (52210854534752474337/12500000000000000000)
  directionHi := (417686836278019794697/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree071.table
  base := (765100260918953349952314001941592856659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-18554145118770498288368535114388311000000000000)
      constant := (311390773147533434523231511510256879469449862891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree071.table
  base := (382534315598120939393371979591113564869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-8424259702596867824468500315166500000000000)
      constant := (141800575006125052443024465811536283993835418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52210854534752474337/12500000000000000000)
  centralHi := (417686836278019794697/100000000000000000000)
  directionLo := (210329866919932574729/50000000000000000000)
  directionHi := (420659733839865149459/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree072.table
  base := (2150555754647198390866112710943706643487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-37631446180733745170729062183824737000000000000)
      constant := (640925455029251672599372600146745361919142064663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree072.table
  base := (2150500706790154033495888145790475333327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-17086050638466181377647309883593000000000000)
      constant := (291862236226018170519847939016366361595331047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210329866919932574729/50000000000000000000)
  centralHi := (420659733839865149459/100000000000000000000)
  directionLo := (423611768189354088743/100000000000000000000)
  directionHi := (52951471023669261093/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree073.table
  base := (558398266163359141513651530066966127011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-38154602123926493764721054138872852000000000000)
      constant := (659333252670949930259602077772597218230093974695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree073.table
  base := (1395971718928443606599758305117518150367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-8661790935869313553178809568426500000000000)
      constant := (150121723428490884235124216040541924052282487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423611768189354088743/100000000000000000000)
  centralHi := (52951471023669261093/12500000000000000000)
  directionLo := (85308674499794202477/20000000000000000000)
  directionHi := (213271686249485506193/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree074.table
  base := (1727250993975877191234372046939578336221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-19338879033559621179356523046960483500000000000)
      constant := (339002467511835028057972050685301493804641100229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree074.table
  base := (863615081935688848128721773221593554193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-8780556552505536417533964195056500000000000)
      constant := (154372390026993537381922613146116990546127346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85308674499794202477/20000000000000000000)
  centralHi := (213271686249485506193/50000000000000000000)
  directionLo := (429454965155929727613/100000000000000000000)
  directionHi := (214727482577964863807/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree075.table
  base := (258630200614498923536748426306618555451/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-19600457005155995476352519024484541000000000000)
      constant := (348470249242978427155493015058367985470906755992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree075.table
  base := (103451174446643474717171311329676088747/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-8899322169141759281889118821686500000000000)
      constant := (158683117114572990165631856766037761360753340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429454965155929727613/100000000000000000000)
  centralHi := (214727482577964863807/50000000000000000000)
  directionLo := (13510842201849846523/3125000000000000000)
  directionHi := (432346950459195088737/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree076.table
  base := (1210682780166032868149497145060876838057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (172302)
      previous := (86151)
      next := (86151)
      square := (767114757746831308071744357385000000000000)
      linear := (-55019487470228171117308905822738500000000000)
      constant := (991883573361582817375663571522452453870535826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree076.table
  base := (968539923050537526538916076913416463539/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (156)
      previous := (78)
      next := (78)
      square := (694535769802472890965816530000000000000)
      linear := (-49961705184365552056754977553000000000000)
      constant := (903345728588407694984175549412567082317695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13510842201849846523/3125000000000000000)
  centralHi := (432346950459195088737/100000000000000000000)
  directionLo := (217609859637408529951/50000000000000000000)
  directionHi := (435219719274817059903/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree077.table
  base := (556844239431796674552738236669331430009/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-20123612948348744070344510979532656000000000000)
      constant := (367801628407284323432464293291467206335146235205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree077.table
  base := (5568415003612314480054345201733129156253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-18273706804828410021198856149893000000000000)
      constant := (334969500259493512887057580737426659625407333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217609859637408529951/50000000000000000000)
  centralHi := (435219719274817059903/100000000000000000000)
  directionLo := (438073649652584609947/100000000000000000000)
  directionHi := (109518412413146152487/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree078.table
  base := (3157607088212019049502182962295875093811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-20385190919945118367340506957056713500000000000)
      constant := (377665223376130174270601653090159268797684488139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree078.table
  base := (6315190367046615349239594648665383432633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-18511238038100855749909165403153000000000000)
      constant := (343951309944281805815043250366122203419180513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438073649652584609947/100000000000000000000)
  centralHi := (109518412413146152487/25000000000000000000)
  directionLo := (13778409606461054883/3125000000000000000)
  directionHi := (440909107406753756257/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree079.table
  base := (1770761004377570909521867640951752944693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-20646768891541492664336502934580771000000000000)
      constant := (387660753913404426443997039082943065055484976314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree079.table
  base := (7083023324604625703545387112947059801079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-18748769271373301478619474656413000000000000)
      constant := (353053236215256758475493898301940888588189519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13778409606461054883/3125000000000000000)
  centralHi := (440909107406753756257/100000000000000000000)
  directionLo := (443726446663375244827/100000000000000000000)
  directionHi := (110931611665843811207/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree080.table
  base := (7871929815613426178653531049213578823491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-41816693726275733922664997824209657000000000000)
      constant := (795576438362005646478099068546051579219214074459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree080.table
  base := (7871911834137669957326279488939699124981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-18986300504645747207329783909673000000000000)
      constant := (362275278335202698981991519583747231384118141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443726446663375244827/100000000000000000000)
  centralHi := (110931611665843811207/25000000000000000000)
  directionLo := (446526010376540183739/100000000000000000000)
  directionHi := (22326300518827009187/5000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree081.table
  base := (8681869767022636990200987771785510594791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-42339849669468482516656989779257772000000000000)
      constant := (816095236919483332651208539112156757513305488159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree081.table
  base := (2778193326122952705484507945095303507/3200000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-19223831737918192936040093162933000000000000)
      constant := (371617435671823968287490624625733639268834375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446526010376540183739/100000000000000000000)
  centralHi := (22326300518827009187/5000000000000000000)
  directionLo := (89861626163134828447/20000000000000000000)
  directionHi := (112327032703918535559/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree082.table
  base := (4756431162001583284236605253384248840673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-21431502806330615555324490867152943500000000000)
      constant := (418438951132501191574951272174050782853745843177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree082.table
  base := (237821218810009742917034810652672361941/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-9730681485595319332375201208096500000000000)
      constant := (190539853841414282850946770227895294453214020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89861626163134828447/20000000000000000000)
  centralHi := (112327032703918535559/25000000000000000000)
  directionLo := (220738833020429571/48828125000000000)
  directionHi := (452073130025839761409/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree083.table
  base := (5182453079255456011036132040913108270739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-21693080777926989852320486844677001000000000000)
      constant := (428962216669757678083769346124320787464892544811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree083.table
  base := (10364894370613047430465968140098688296053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-19698894204463084393460711669453000000000000)
      constant := (390662093903131848492461878256194626474875133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220738833020429571/48828125000000000)
  centralHi := (452073130025839761409/100000000000000000000)
  directionLo := (227410660131426501437/50000000000000000000)
  directionHi := (3638570562102824023/800000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree084.table
  base := (2247600026209805466079554740903383554969/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-43909317499046728298632965644402117000000000000)
      constant := (879234829234331631341835234535918904562632370405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree084.table
  base := (11237989893911186758269950146492775988961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-19936425437735530122171020922713000000000000)
      constant := (400364593933878990754027684006015892132014921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227410660131426501437/50000000000000000000)
  centralHi := (3638570562102824023/800000000000000000)
  directionLo := (57194125550609650143/12500000000000000000)
  directionHi := (91510600880975440229/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree085.table
  base := (1213214326393796361453151150746890201999/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-22216236721119738446312478799725116000000000000)
      constant := (450404544584900815049423854657662930160969502755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree085.table
  base := (6066067187404649946969716866334673288633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-10086978335503987925440665087986500000000000)
      constant := (205093603716513862084284699051999317057196513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57194125550609650143/12500000000000000000)
  centralHi := (91510600880975440229/20000000000000000000)
  directionLo := (460268476342030675173/100000000000000000000)
  directionHi := (230134238171015337587/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree086.table
  base := (13047334718373564974430619616417541756717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-44955629385432225486616949554498347000000000000)
      constant := (922647212477021817120242839617887989256352214933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree086.table
  base := (6523663500409326699979858534795254630183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-10205743952140210789795819714616500000000000)
      constant := (210064967053634807982572106594930086921496063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460268476342030675173/100000000000000000000)
  centralHi := (230134238171015337587/50000000000000000000)
  directionLo := (462968021345426543089/100000000000000000000)
  directionHi := (46296802134542654309/10000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree087.table
  base := (6991786887368228046070145689527991818341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-22739392664312487040304470754773231000000000000)
      constant := (472374599291066220589046441416764921735044212109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree087.table
  base := (6991783537624728742798203374179353951633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-10324509568776433654150974341246500000000000)
      constant := (215096386852549826014648506621494246776539513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462968021345426543089/100000000000000000000)
  centralHi := (46296802134542654309/10000000000000000000)
  directionLo := (465651916416956457829/100000000000000000000)
  directionHi := (46565191641695645783/10000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree088.table
  base := (3735214953923003314236770892730052711469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-23000970635908861337300466732297288500000000000)
      constant := (483557523496420311964456557188172908609416485162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree088.table
  base := (933803375046366556664983976073908417939/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-10443275185412656518506128967876500000000000)
      constant := (220187863005435463752934037604793447511007832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465651916416956457829/100000000000000000000)
  centralHi := (46565191641695645783/10000000000000000000)
  directionLo := (468320430621032247771/100000000000000000000)
  directionHi := (117080107655258061943/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree089.table
  base := (994949519480343103320448012663536158949/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-23262548607505235634296462709821346000000000000)
      constant := (494872378643426731039625691670010968908841768808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree089.table
  base := (15919187265137973694903678056100158544441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-21124081604097758765722567189013000000000000)
      constant := (450678790839694439784342235176849157234543201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468320430621032247771/100000000000000000000)
  centralHi := (117080107655258061943/25000000000000000000)
  directionLo := (470973825399410020041/100000000000000000000)
  directionHi := (235486912699705010021/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree090.table
  base := (8459285404246447766659532846383795500093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-23524126579101609931292458687345403500000000000)
      constant := (506319164550975244614532012596934151337753662757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree090.table
  base := (16918566429362123309122437612468046931557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-21361612837370204494432876442273000000000000)
      constant := (461101968033063875409322549289370964942292077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470973825399410020041/100000000000000000000)
  centralHi := (235486912699705010021/50000000000000000000)
  directionLo := (236806177435069686793/50000000000000000000)
  directionHi := (473612354870139373587/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree091.table
  base := (17938994916536324812089035022747138454741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-47571409101395968456576909329738922000000000000)
      constant := (1035795762127463193748427988596322539188594755709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree091.table
  base := (17938991117024056721385204635502642877857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-21599144070642650223143185695533000000000000)
      constant := (471645257455102351593733212375219454078906377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236806177435069686793/50000000000000000000)
  centralHi := (473612354870139373587/100000000000000000000)
  directionLo := (119059066527901316609/25000000000000000000)
  directionHi := (476236266111605266437/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree092.table
  base := (2372558037714212062619644342442552481579/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-24047282522294358525284450642393518500000000000)
      constant := (529608528048481102627580474332299723635530767884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree092.table
  base := (18980461005500084473357802782100758966079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-21836675303915095951853494948793000000000000)
      constant := (482308658989342716443115586774534373986754519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119059066527901316609/25000000000000000000)
  centralHi := (476236266111605266437/100000000000000000000)
  directionLo := (239422899716280576281/50000000000000000000)
  directionHi := (478845799432561152563/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree093.table
  base := (1252686167345519233600275661188220558893/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-24308860493890732822280446619917576000000000000)
      constant := (541451105390990507274204734896389056309249311656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree093.table
  base := (4008595163656437147825456285348061101053/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-22074206537187541680563804202053000000000000)
      constant := (493092172535965574439315097311502250287400665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239422899716280576281/50000000000000000000)
  centralHi := (478845799432561152563/100000000000000000000)
  directionLo := (481441188628988679423/100000000000000000000)
  directionHi := (1880629643081987029/390625000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree094.table
  base := (52816344495835009032146655308193077971/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-11122878436164376242316180442481500000000000)
      constant := (250532192391722349715257840148655040229506200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree094.table
  base := (264081691480185438815193372090603500293/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-11155868885229993704637056727656500000000000)
      constant := (251997899004714990454033062163269314544230920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481441188628988679423/100000000000000000000)
  centralHi := (1880629643081987029/390625000000000000)
  directionLo := (96804532245712201347/20000000000000000000)
  directionHi := (30251416326785062921/6250000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree095.table
  base := (4446228290707573766225167417448703026641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (344604)
      previous := (172302)
      next := (172302)
      square := (1534229515493662616143488714770000000000000)
      linear := (-137573498266390478760512125069062000000000000)
      constant := (3133141555520692728604996551985770299929249845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree095.table
  base := (11115569651432477449444419610136456934987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (347267884901236445482908265000000000000)
      linear := (-31231674520405032047069837546500000000000)
      constant := (713323456144655117464697872577636456934987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96804532245712201347/20000000000000000000)
  centralHi := (30251416326785062921/6250000000000000000)
  directionLo := (486590438723433210773/100000000000000000000)
  directionHi := (243295219361716605387/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree096.table
  base := (4671357892524949587580524587882051664879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-50187188817359711426536869104979497000000000000)
      constant := (1155540837307051586299555110188161203090530468355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree096.table
  base := (11678393798846182184624015832384702018727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-11393400118502439433347365980916500000000000)
      constant := (263081692227103105446288824026674877428760447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486590438723433210773/100000000000000000000)
  centralHi := (243295219361716605387/50000000000000000000)
  directionLo := (24457236839601693147/5000000000000000000)
  directionHi := (489144736792033862941/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree097.table
  base := (245034816708871283983172313210909082453/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-25355172380276230010264430530013806000000000000)
      constant := (590140716577751261849021114892903054782153119850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree097.table
  base := (24503480053906946079955685056062906974319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-23024331470277324595405041215093000000000000)
      constant := (537427345308940196762745688785299709417729159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24457236839601693147/5000000000000000000)
  centralHi := (489144736792033862941/100000000000000000000)
  directionLo := (245842882755243171849/50000000000000000000)
  directionHi := (491685765510486343699/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree098.table
  base := (1604451121610026497321254514924398646877/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-25616750351872604307260426507537863500000000000)
      constant := (602642944491304695238609266374537567212427334184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree098.table
  base := (25671216543914920233829634771015687835789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-23261862703549770324115350468353000000000000)
      constant := (548811417854581597913233224767950663308719829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245842882755243171849/50000000000000000000)
  centralHi := (491685765510486343699/100000000000000000000)
  directionLo := (494213729554246436867/100000000000000000000)
  directionHi := (123553432388561609217/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree099.table
  base := (26859998173677860473853255613320907383379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-51756656646937957208512844970123842000000000000)
      constant := (1230554204697808476165502168152210076646968200171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree099.table
  base := (6714999239617622496696076382516768339651/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-11749696968411108026412829860806500000000000)
      constant := (280157801025846340841662681662690606741228022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494213729554246436867/100000000000000000000)
  centralHi := (123553432388561609217/25000000000000000000)
  directionLo := (99345765678100788173/20000000000000000000)
  directionHi := (248364414195251970433/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree100.table
  base := (28069822257371324132042128760347359546147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-52279812590130705802504836925171957000000000000)
      constant := (1256086380223533420668107087626740566522715379003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree100.table
  base := (438590956313453463975356353658509984839/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-11868462585047330890767984487436500000000000)
      constant := (285969948933257693663697413457613107344860128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99345765678100788173/20000000000000000000)
  centralHi := (248364414195251970433/50000000000000000000)
  directionLo := (499231256461860158039/100000000000000000000)
  directionHi := (12480781411546503951/2500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree101.table
  base := (1831293132097185434461710154498297197463/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-26401484266661727198248414440110036000000000000)
      constant := (640941207746684003899487811207579182752057375096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree101.table
  base := (586013784013282672657837904731269993251/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-11987228201683553755123139114066500000000000)
      constant := (291842152635080817521565297434916211689090275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499231256461860158039/100000000000000000000)
  centralHi := (12480781411546503951/2500000000000000000)
  directionLo := (62715150420219991501/12500000000000000000)
  directionHi := (501721203361759932009/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree102.table
  base := (30552601670937320970170386527758573774903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-53326124476516202990488820835268187000000000000)
      constant := (1307942310450460927723503260413744995898222622447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree102.table
  base := (30552600879823825396614659280597846736447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-24211987636639553238956587481393000000000000)
      constant := (595548824237918808684119401936721822671857367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62715150420219991501/12500000000000000000)
  centralHi := (501721203361759932009/100000000000000000000)
  directionLo := (504198854002126170637/100000000000000000000)
  directionHi := (252099427001063085319/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree103.table
  base := (3182555686851535981929272568843394982537/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-26924640209854475792240406395158151000000000000)
      constant := (667133032523082689033339395820709572614645740565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree103.table
  base := (1989097261437518380845087623321232064211/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-12224759434955999483833448367326500000000000)
      constant := (303766727374327019703162043786791218201441368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504198854002126170637/100000000000000000000)
  centralHi := (252099427001063085319/50000000000000000000)
  directionLo := (506664388773616314333/100000000000000000000)
  directionHi := (253332194386808157167/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree104.table
  base := (16559777827055272246966299334499459440551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-27186218181450850089236402372682208500000000000)
      constant := (680426839619435817538823045717119438431407954399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree104.table
  base := (8279888765038632381409928293956991196927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-12343525051592222348188602993956500000000000)
      constant := (309819098392151622264138305860232947644181294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506664388773616314333/100000000000000000000)
  centralHi := (253332194386808157167/50000000000000000000)
  directionLo := (20364719347955752013/4000000000000000000)
  directionHi := (254558991849446900163/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree105.table
  base := (17217298991556276643172675646601659753429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-27447796153047224386232398350206266000000000000)
      constant := (693852576496502621160442946532003837906212202621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree105.table
  base := (17217298734267155256793806880268098322869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-12462290668228445212543757620586500000000000)
      constant := (315931525164716436102110039956059283494555709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20364719347955752013/4000000000000000000)
  centralHi := (254558991849446900163/50000000000000000000)
  directionLo := (511559810579283064629/100000000000000000000)
  directionHi := (51155981057928306463/10000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree106.table
  base := (7154136763480251308960822509491898799041/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-55418748249287197366456788655460647000000000000)
      constant := (1414820486278167340525758254967811078026982232045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree106.table
  base := (8942670842908242146534008553311953730803/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-12581056284864668076898912247216500000000000)
      constant := (322104007685432007558020399026990230593639766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511559810579283064629/100000000000000000000)
  centralHi := (51155981057928306463/10000000000000000000)
  directionLo := (102798007427030772227/20000000000000000000)
  directionHi := (32124377320947116321/6250000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree107.table
  base := (4640976640552708608903629687199530444693/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-27970952096239972980224390305254381000000000000)
      constant := (721099839534198494570774901441369597601859952628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree107.table
  base := (18563906369148177549008394010233755285757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-12699821901500890941254066873846500000000000)
      constant := (328336545948675012801398475407339885658158277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102798007427030772227/20000000000000000000)
  centralHi := (32124377320947116321/6250000000000000000)
  directionLo := (129102206785089880461/25000000000000000000)
  directionHi := (103281765428071904369/20000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree108.table
  base := (38505985876390192155206281615976350426941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-56465060135672694554440772565556877000000000000)
      constant := (1469842731341538185638709126904072255671613673509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree108.table
  base := (38505985541956939276101158638113209891917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-25637175036274227611218443000953000000000000)
      constant := (669258279899300025055389071521802868770982037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129102206785089880461/25000000000000000000)
  centralHi := (103281765428071904369/20000000000000000000)
  directionLo := (129704085137758526621/25000000000000000000)
  directionHi := (103763268110206821297/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree109.table
  base := (9976300512403384057157978835611054153199/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-28494108039432721574216382260302496000000000000)
      constant := (748874821539348369732985958253996868984328778702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree109.table
  base := (63848322815963135880234729991944498861/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-25874706269546673339928752254213000000000000)
      constant := (681963579368541781682334639399889477555513125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129704085137758526621/25000000000000000000)
  centralHi := (103763268110206821297/20000000000000000000)
  directionLo := (521212733629035077207/100000000000000000000)
  directionHi := (65151591703629384651/12500000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree110.table
  base := (165301846495617367233557897452704065643/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-28755686011029095871212378237826553500000000000)
      constant := (762960207131887130575188115171954573055368088375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree110.table
  base := (41325461373085123067326479936717638903717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-26112237502819119068639061507473000000000000)
      constant := (694788990298118358357638125172485067644241837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521212733629035077207/100000000000000000000)
  centralHi := (65151591703629384651/12500000000000000000)
  directionLo := (523598159060301078883/100000000000000000000)
  directionHi := (130899539765075269721/25000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree111.table
  base := (21383382291039897241326895686689752140213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-29017263982625470168208374215350611000000000000)
      constant := (777177522441534166261013250284889604341960716637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree111.table
  base := (1069169109122338553529888137605008859139/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-13174884368045782398674685380366500000000000)
      constant := (353867256341056864016308950185039663962983580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523598159060301078883/100000000000000000000)
  centralHi := (130899539765075269721/25000000000000000000)
  directionLo := (262986383034189255283/50000000000000000000)
  directionHi := (525972766068378510567/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree112.table
  base := (44229110909531461754461813635289902701771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-58557683908443688930408740385749337000000000000)
      constant := (1583053534924929473694652037742926141619624582179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree112.table
  base := (22114555360741754222438350136072336555041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-13293649984682005263029840006996500000000000)
      constant := (360400073257751618432948158243450113496369801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262986383034189255283/50000000000000000000)
  centralHi := (525972766068378510567/100000000000000000000)
  directionLo := (528336700523355750513/100000000000000000000)
  directionHi := (264168350261677875257/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree113.table
  base := (45712500593856253044299734329631503983301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-59080839851636437524400732340797452000000000000)
      constant := (1612015884379466852488710136129125351094979399149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree113.table
  base := (45712500431050301798848131776077361771837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-26824831202636456254769989267253000000000000)
      constant := (733985891794025380872665977563272927599633157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528336700523355750513/100000000000000000000)
  centralHi := (264168350261677875257/50000000000000000000)
  directionLo := (132672526261607516093/25000000000000000000)
  directionHi := (530690105046430064373/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree114.table
  base := (15109418759852746908958253810784538821/3200000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (344604)
      previous := (172302)
      next := (172302)
      square := (1534229515493662616143488714770000000000000)
      linear := (-165108021592324615286406438492647000000000000)
      constant := (4546376989579766824270260153294970019548715625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree114.table
  base := (23608466741799321561112052191197409636017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (347267884901236445482908265000000000000)
      linear := (-37482496448627288065762186316500000000000)
      constant := (1035030122595667402084109612542197409636017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132672526261607516093/25000000000000000000)
  centralHi := (530690105046430064373/100000000000000000000)
  directionLo := (266516559555159654799/50000000000000000000)
  directionHi := (533033119110319309599/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree115.table
  base := (4874240999268505586237716452432055636113/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-30063575869010967356192358125446841000000000000)
      constant := (835366080747160682157927675853654833862313378685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree115.table
  base := (48742409870681584531100759841773395103369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-27299893669181347712190607773773000000000000)
      constant := (760717716672593338975990511735475195632316209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266516559555159654799/50000000000000000000)
  centralHi := (533033119110319309599/100000000000000000000)
  directionLo := (133841469783929620133/25000000000000000000)
  directionHi := (535365879135718480533/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree116.table
  base := (25144464845389506330704613416863968210261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-30325153840607341653188354102970898500000000000)
      constant := (850243044570776157807595359672163403085304424189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree116.table
  base := (50288929585176656789871246997841087570187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-27537424902453793440900917027033000000000000)
      constant := (774263796267018593492402018735848632612837507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133841469783929620133/25000000000000000000)
  centralHi := (535365879135718480533/100000000000000000000)
  directionLo := (537688518583989855469/100000000000000000000)
  directionHi := (53768851858398985547/10000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree117.table
  base := (5185649271249324920169822806427664076709/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-30586731812203715950184350080494956000000000000)
      constant := (865251938087471028560145164202538809389037576705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree117.table
  base := (51856492621093972592881658939257191628119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-27774956135726239169611226280293000000000000)
      constant := (787929987295185278536620600861592846177750959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537688518583989855469/100000000000000000000)
  centralHi := (53768851858398985547/10000000000000000000)
  directionLo := (540001168046264951843/100000000000000000000)
  directionHi := (135000292011566237961/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree118.table
  base := (13361274763128103327420383412902768611567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-30848309783800090247180346058019013500000000000)
      constant := (880392761295125933277849414759425650353050985166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree118.table
  base := (53445098973411737913606816632396124323013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-28012487368998684898321535533553000000000000)
      constant := (801716289755280526465070668481569000880607693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540001168046264951843/100000000000000000000)
  centralHi := (135000292011566237961/25000000000000000000)
  directionLo := (135575988832281653943/25000000000000000000)
  directionHi := (542303955329126615773/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree119.table
  base := (27527374353193658819416833577667774067399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-31109887755396464544176342035543071000000000000)
      constant := (895665514191966871960558414011865374949773265151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree119.table
  base := (55054748637935270280659605847434458247991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-28250018602271130627031844786813000000000000)
      constant := (815622703645790056905581473358810839427524751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135575988832281653943/25000000000000000000)
  centralHi := (542303955329126615773/100000000000000000000)
  directionLo := (272298502768515159469/50000000000000000000)
  directionHi := (544597005537030318939/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree120.table
  base := (56685441670408946059265842940025662581003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-62742931453985677682344676026134257000000000000)
      constant := (1822140393553029938012780641703532414599558261347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree120.table
  base := (56685441611176177551011300715993340746927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-28487549835543576355742154040073000000000000)
      constant := (829649228965454560294519645454833596009640647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272298502768515159469/50000000000000000000)
  centralHi := (544597005537030318939/100000000000000000000)
  directionLo := (546880441151615064561/100000000000000000000)
  directionHi := (273440220575807532281/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree121.table
  base := (182303681067188848574364433226514561917/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-31633043698589213138168333990591186000000000000)
      constant := (926606809047543402148365728259596456679283957280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree121.table
  base := (911518404535137915835456041280771817001/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-14362540534408011042226231646666500000000000)
      constant := (421897932856616161539372307400221976029995552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546880441151615064561/100000000000000000000)
  centralHi := (273440220575807532281/50000000000000000000)
  directionLo := (549154382108046173843/100000000000000000000)
  directionHi := (137288595527011543461/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree122.table
  base := (6000995751712445392397026963092302850537/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-31894621670185587435164329968115243500000000000)
      constant := (942275351004040479670977211671369901079289400565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree122.table
  base := (2400398298911265587040039067242159895977/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-28962612302088467813162772546593000000000000)
      constant := (858062613888267205675332725808746493061192425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549154382108046173843/100000000000000000000)
  centralHi := (137288595527011543461/25000000000000000000)
  directionLo := (11028378917370491937/2000000000000000000)
  directionHi := (551418945868524596851/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree123.table
  base := (61703780395203867695640227311384878382803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-64312399283563923464320651891278602000000000000)
      constant := (1916151645290355985543313365171568080256487869547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree123.table
  base := (61703780356841105982591725323944194040511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-29200143535360913541873081799853000000000000)
      constant := (872449473489861210701362583150882854048624471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11028378917370491937/2000000000000000000)
  centralHi := (551418945868524596851/100000000000000000000)
  directionLo := (553674247493090232363/100000000000000000000)
  directionHi := (138418561873272558091/25000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree124.table
  base := (63418646574053680580473416658177189775669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-64835555226756672058312643846326717000000000000)
      constant := (1948016447940568187493443849667488364809417468381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree124.table
  base := (63418646540866697216383067711958128445647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-29437674768633359270583391053113000000000000)
      constant := (886956444517450987434448317112868884368878567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553674247493090232363/100000000000000000000)
  centralHi := (138418561873272558091/25000000000000000000)
  directionLo := (111184079941568003489/20000000000000000000)
  directionHi := (277960199853920008723/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree125.table
  base := (32577278026161385031882407034640203448037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-32679355584974710326152317900687416000000000000)
      constant := (990072554978820056947058435232046881536933657613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree125.table
  base := (32577278011807566275595193618969838531217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-14837603000952902499646850153186500000000000)
      constant := (450791763485293855748168640549760611709769337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111184079941568003489/20000000000000000000)
  centralHi := (277960199853920008723/50000000000000000000)
  directionLo := (279078756485337614837/50000000000000000000)
  directionHi := (22326300518827009187/4000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree126.table
  base := (16727877207235988466825600585239684296277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-32940933556571084623148313878211473500000000000)
      constant := (1006268815670360370652377266327141185504763594746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree126.table
  base := (66911508804112660382904126663444690821139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-29912737235178250728004009559633000000000000)
      constant := (916330720848919858557945924947761533386431179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279078756485337614837/50000000000000000000)
  centralHi := (22326300518827009187/4000000000000000000)
  directionLo := (560385695534686505393/100000000000000000000)
  directionHi := (280192847767343252697/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree127.table
  base := (34344752451545613315968182954683744437609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-33202511528167458920144309855735531000000000000)
      constant := (1022597006044575686288854087483240901505526859441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree127.table
  base := (68689504881614213412908890601277652683587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-30150268468450696456714318812893000000000000)
      constant := (931198026152178459324474090922812232618774907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560385695534686505393/100000000000000000000)
  centralHi := (280192847767343252697/50000000000000000000)
  directionLo := (281302526754639745383/50000000000000000000)
  directionHi := (562605053509279490767/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree128.table
  base := (70488544274143143572676012151771862092691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-66928178999527666434280611666519177000000000000)
      constant := (2078114252202436437190631754559384815653954345259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree128.table
  base := (35244272127784228217304980722792220888261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-15193899850861571092712314033076500000000000)
      constant := (473092721440082240893170542984479991740662221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281302526754639745383/50000000000000000000)
  centralHi := (562605053509279490767/100000000000000000000)
  directionLo := (564815690919138784991/100000000000000000000)
  directionHi := (17650490341223087031/3125000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree129.table
  base := (9038578367706434559148461922014362564267/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-33725667471360207514136301810783646000000000000)
      constant := (1055649175840109248000319111004753140587548619532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree129.table
  base := (9038578365698485715460505859287100420137/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-15312665467497793957067468659706500000000000)
      constant := (480646485516369018549533100778969073006677828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564815690919138784991/100000000000000000000)
  centralHi := (17650490341223087031/3125000000000000000)
  directionLo := (283508854880561442599/50000000000000000000)
  directionHi := (567017709761122885199/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree130.table
  base := (74149752905314391491303507238337813973661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-67974490885913163622264595576615407000000000000)
      constant := (2144746310522256851912124620975784861415481990789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree130.table
  base := (74149752891423258640365866191252528712507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-30862862168268033642845246572673000000000000)
      constant := (976520610609809148669694171358432162865215027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283508854880561442599/50000000000000000000)
  centralHi := (567017709761122885199/100000000000000000000)
  directionLo := (56921121005917817987/10000000000000000000)
  directionHi := (569211210059178179871/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree131.table
  base := (38005961082476752378872836593986590956473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-34248823414552956108128293765831761000000000000)
      constant := (1089229064364204626443459629710362431159148437377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree131.table
  base := (76011922152941734738298589857716083235181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-31100393401540479371555555825933000000000000)
      constant := (991868361611329861097090179906958506047900341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56921121005917817987/10000000000000000000)
  centralHi := (569211210059178179871/100000000000000000000)
  directionLo := (285698144958677821759/50000000000000000000)
  directionHi := (571396289917355643519/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree132.table
  base := (38947567360247131580111745799812818467043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-34510401386149330405124289743355818500000000000)
      constant := (1106216903149308123310089514811928186773724973307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree132.table
  base := (15579026942021639551745381084220498523137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-31337924634812925100265865079193000000000000)
      constant := (1007336224037287497411843559408133999834262285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285698144958677821759/50000000000000000000)
  centralHi := (571396289917355643519/100000000000000000000)
  directionLo := (573573045571009742283/100000000000000000000)
  directionHi := (143393261392752435571/25000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree133.table
  base := (39899695285974588077263021227119805370947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (172302)
      previous := (86151)
      next := (86151)
      square := (767114757746831308071744357385000000000000)
      linear := (-96321272459129375906150375958116000000000000)
      constant := (3111735932455523280837830301422304087564421923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree133.table
  base := (3989969528148465172336763551954499956363/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (347267884901236445482908265000000000000)
      linear := (-43733318376849544084454535086500000000000)
      constant := (1416792517849998476922340442184044999563630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573573045571009742283/100000000000000000000)
  centralHi := (143393261392752435571/25000000000000000000)
  directionLo := (575741571436255152093/100000000000000000000)
  directionHi := (287870785718127576047/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree134.table
  base := (20431172429850872942524627379349184304583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-35033557329342078999116281698403933500000000000)
      constant := (1140588369765645960138477817889272851849010817534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree134.table
  base := (3268987588465594517538591820541230676361/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-31812987101357816557686483585713000000000000)
      constant := (1038632283162605516695495839730666606854158025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575741571436255152093/100000000000000000000)
  centralHi := (287870785718127576047/50000000000000000000)
  directionLo := (72237745019719150363/12500000000000000000)
  directionHi := (115580392031550640581/20000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree135.table
  base := (41835516081501483878218126910036763074779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-35295135300938453296112277675927991000000000000)
      constant := (1157971997596972407763941415118787008864719438771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree135.table
  base := (41835516078145613531167803878060984048209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-16025259167315131143198396419486500000000000)
      constant := (527230239931034602066800673683307515241403449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72237745019719150363/12500000000000000000)
  centralHi := (115580392031550640581/20000000000000000000)
  directionLo := (29002715132744824027/5000000000000000000)
  directionHi := (580054302654896480541/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree136.table
  base := (42819208951471719200812735248471768883471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-35556713272534827593108273653452048500000000000)
      constant := (1175487555110501331187447554613969394624355065479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree136.table
  base := (21409604474285346145925264529292671740011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-16144024783951354007553551046116500000000000)
      constant := (535204393993084328298269440820593308996287942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29002715132744824027/5000000000000000000)
  centralHi := (580054302654896480541/100000000000000000000)
  directionLo := (36387418010403545543/6250000000000000000)
  directionHi := (582198688166456728689/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree137.table
  base := (43813423469730960053455293231889424126229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-35818291244131201890104269630976106000000000000)
      constant := (1193135042306327234655074219874597772317537189821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree137.table
  base := (5476677933402908020328333020174069761551/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-16262790400587576871908705672746500000000000)
      constant := (543238603767498179846650160078753213471359288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36387418010403545543/6250000000000000000)
  centralHi := (582198688166456728689/100000000000000000000)
  directionLo := (584335204293758085763/100000000000000000000)
  directionHi := (146083801073439521441/25000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree138.table
  base := (17927263854565807063619608044584931764793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-72159738431455152374200531217000327000000000000)
      constant := (2421828918369116043932428720378600962254512065285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree138.table
  base := (44818159634246939089644641975698268055171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-16381556017223799736263860299376500000000000)
      constant := (551332869254327999902502415694694074767916731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584335204293758085763/100000000000000000000)
  centralHi := (146083801073439521441/25000000000000000000)
  directionLo := (586463937042434753259/100000000000000000000)
  directionHi := (29323196852121737663/5000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree139.table
  base := (18333366980668513150294187568870587726127/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-72682894374647900968192523172048442000000000000)
      constant := (2457651611490624851973604197768548118933061250115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree139.table
  base := (9166683489959558011995675807209320755797/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-16500321633860022600619014926006500000000000)
      constant := (559487190453630130814159891537386323964213585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586463937042434753259/100000000000000000000)
  centralHi := (29323196852121737663/5000000000000000000)
  directionLo := (147146242715707353409/25000000000000000000)
  directionHi := (588584970862829413637/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree140.table
  base := (46859196915660986371499532673326744843053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-36603025158920324781092257563548278500000000000)
      constant := (1246869081988717823778291320904887716848347771797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree140.table
  base := (23429598457020881533391461371518237030897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-16619087250496245464974169552636500000000000)
      constant := (567701567365464479085151559718446167136307634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147146242715707353409/25000000000000000000)
  centralHi := (588584970862829413637/100000000000000000000)
  directionLo := (73837298586135760841/12500000000000000000)
  directionHi := (590698388689086086729/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree141.table
  base := (95790996057103745625227961271249652684809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-33376734387068084271696019503008000000000000)
      constant := (1145354719705666257928072955937800999619216049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree141.table
  base := (95790996054304962121816723144804908469703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-33475705734264936658658648358533000000000000)
      constant := (1151951999979787445201468604355227571957562783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73837298586135760841/12500000000000000000)
  centralHi := (590698388689086086729/100000000000000000000)
  directionLo := (296402135988494312681/50000000000000000000)
  directionHi := (592804271976988625363/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree142.table
  base := (97884641581037458837243163942072681943327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-74252362204226146750168499037192787000000000000)
      constant := (2566702847048046968380070074789909697143024172823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree142.table
  base := (48942320789309384909334900356105063998697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-16856618483768691193684478805896500000000000)
      constant := (584310488326982639513887972859226928103529617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296402135988494312681/50000000000000000000)
  centralHi := (592804271976988625363/100000000000000000000)
  directionLo := (29745135037029684727/5000000000000000000)
  directionHi := (594902700740593694541/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree143.table
  base := (49999665201741217731896738555735486466197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-37387759073709447672080245496120451000000000000)
      constant := (1301790488816206401621031617991601888134482331453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree143.table
  base := (24999832600348081261156800756948198190813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-16975384100404914058039633432526500000000000)
      constant := (592705032376797541160213205296816099093766986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29745135037029684727/5000000000000000000)
  centralHi := (594902700740593694541/100000000000000000000)
  directionLo := (149248438396926211653/25000000000000000000)
  directionHi := (596993753587704846613/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree144.table
  base := (102135062524804929478482536461602014997507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-75298674090611643938152482947289017000000000000)
      constant := (2640722967583206337214088888917585453257746959643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree144.table
  base := (102135062522998848586775593885316073722543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-34188299434082273844789576118313000000000000)
      constant := (1202319264278811587783558284610311102613838023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149248438396926211653/25000000000000000000)
  centralHi := (596993753587704846613/100000000000000000000)
  directionLo := (599077507754232189647/100000000000000000000)
  directionHi := (37442344234639511853/6250000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree145.table
  base := (13036479743171968934361190203178861680993/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-37910915016902196266072237451168566000000000000)
      constant := (1339064408450361636416593078406091551212084747428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree145.table
  base := (5214591897190758898439469530239850199947/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-17212915333677359786749942685786500000000000)
      constant := (609674287614875416881609016210508359221808670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599077507754232189647/100000000000000000000)
  centralHi := (37442344234639511853/6250000000000000000)
  directionLo := (601154039137480141087/100000000000000000000)
  directionHi := (18786063723046254409/3125000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree146.table
  base := (106469656665568273402073442738984679521419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-76344985976997141126136466857385247000000000000)
      constant := (2715798525585261355186760198240961375699676060131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree146.table
  base := (53234828332109949322533209462315944998629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-17331680950313582651105097312416500000000000)
      constant := (618248998803274744804221634558655056144505069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601154039137480141087/100000000000000000000)
  centralHi := (18786063723046254409/3125000000000000000)
  directionLo := (603223422328403857139/100000000000000000000)
  directionHi := (30161171116420192857/5000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree147.table
  base := (54334259342878378514532415378463216157231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-38434070960094944860064229406216681000000000000)
      constant := (1376866046818559519474131320541592687448867703719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree147.table
  base := (13583564835573972744988788742052777819841/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-17450446566949805515460251939046500000000000)
      constant := (626883765704672145887263802761629711171850404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603223422328403857139/100000000000000000000)
  centralHi := (30161171116420192857/5000000000000000000)
  directionLo := (605285730642873124231/100000000000000000000)
  directionHi := (75660716330359140529/12500000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree148.table
  base := (55444212003157479381430020044757464701231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-38695648931691319157060225383740738500000000000)
      constant := (1395964760528297187895348160583480775968531959719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree148.table
  base := (554442120026542423821671603653777316857/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-17569212183586028379815406565676500000000000)
      constant := (635578588319135787192343413724283361138537700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605285730642873124231/100000000000000000000)
  centralHi := (75660716330359140529/12500000000000000000)
  directionLo := (151835259037995196673/25000000000000000000)
  directionHi := (607341036151980786693/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree149.table
  base := (113129372627614970221666200390130719116787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-77914453806575386908112442722529592000000000000)
      constant := (2830390807843984089802908895827248571703962676363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree149.table
  base := (11312937262674547205819604729054559691563/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-17687977800222251244170561192306500000000000)
      constant := (644333466646733440151934763521531980243271215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151835259037995196673/25000000000000000000)
  centralHi := (607341036151980786693/100000000000000000000)
  directionLo := (761736762139288949/125000000000000000)
  directionHi := (609389409711431159201/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree150.table
  base := (115391364550026259778954937437321494885559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-78437609749768135502104434677577707000000000000)
      constant := (2869115953999582813169856939569523513774994138991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree150.table
  base := (115391364549275129577151488642979385593681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-35613486833716948217051431637873000000000000)
      constant := (1306296801375064640782647519955565558199318841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (761736762139288949/125000000000000000)
  centralHi := (609389409711431159201/100000000000000000000)
  directionLo := (152857730247510582169/25000000000000000000)
  directionHi := (611430920990042328677/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree151.table
  base := (3677324992934840165029684224498220001213/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-39480382846480442048048213316312911000000000000)
      constant := (1454052479761841229177476825520173634855456890192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree151.table
  base := (23534879954653207600746315631913086722629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-35851018066989393945761740891133000000000000)
      constant := (1324046780883197913447414473133186121534345345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152857730247510582169/25000000000000000000)
  centralHi := (611430920990042328677/100000000000000000000)
  directionLo := (122693127699478956693/20000000000000000000)
  directionHi := (306732819248697391733/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree152.table
  base := (29994619574910713104450054527963931541251/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (172302)
      previous := (86151)
      next := (86151)
      square := (767114757746831308071744357385000000000000)
      linear := (-110088534122096444169097532669908500000000000)
      constant := (4082213053208548069852912431243261649549246918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree152.table
  base := (119978478299082384562403894784196871257771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (156)
      previous := (78)
      next := (78)
      square := (694535769802472890965816530000000000000)
      linear := (-99968280610143600206293767713000000000000)
      constant := (3717221251573402132648762278600196871257771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122693127699478956693/20000000000000000000)
  centralHi := (306732819248697391733/50000000000000000000)
  directionLo := (38468351850666088349/6250000000000000000)
  directionHi := (123098725922131482717/20000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree153.table
  base := (122303600127567596897552278368388982990697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-80007077579346381284080410542722052000000000000)
      constant := (2986874548678535594154350183943902143971948331953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree153.table
  base := (122303600127083491256468995599996606041191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-36326080533534285403182359397653000000000000)
      constant := (1359907074179595125342205149387027774780869951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38468351850666088349/6250000000000000000)
  centralHi := (123098725922131482717/20000000000000000000)
  directionLo := (308757480300310300189/50000000000000000000)
  directionHi := (617514960600620600379/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree154.table
  base := (124649765258041571718524641110603225592361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-80530233522539129878072402497770167000000000000)
      constant := (3026655132309855184807652018265081639645402687089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree154.table
  base := (124649765257623442002988411379433150406437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-36563611766806731131892668650913000000000000)
      constant := (1378017387968116604109479586179117367296723757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308757480300310300189/50000000000000000000)
  centralHi := (617514960600620600379/100000000000000000000)
  directionLo := (123905939331392970687/20000000000000000000)
  directionHi := (154882424164241213359/25000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree155.table
  base := (127016973691411923533965557119902046074627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-81053389465731878472064394452818282000000000000)
      constant := (3066699575310807310145194442658552911115165226523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree155.table
  base := (31754243422762698372947287950655599874161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-18400571500039588430301488952086500000000000)
      constant := (698123906591844217576527021722730843109144242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123905939331392970687/20000000000000000000)
  centralHi := (154882424164241213359/25000000000000000000)
  directionLo := (621537901912792253323/100000000000000000000)
  directionHi := (155384475478198063331/25000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree156.table
  base := (3235130635700506110414082044796075689369/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-40788272704462313533028193203933198500000000000)
      constant := (1553503938840832186211875316850623978748232393620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree156.table
  base := (64702612713854178398479767059435089444029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-18519337116675811294656643578716500000000000)
      constant := (707299174913217186635337201856530067289294469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (621537901912792253323/100000000000000000000)
  centralHi := (155384475478198063331/25000000000000000000)
  directionLo := (623539639468446817437/100000000000000000000)
  directionHi := (311769819734223408719/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree157.table
  base := (131814520468202387314098201787140830121791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-82099701352117375660048378362914512000000000000)
      constant := (3147580039422694197240675112955367023714792111159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree157.table
  base := (16476815058491629832060704926053934148929/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-18638102733312034159011798205346500000000000)
      constant := (716534498948238020897376821125942380911053476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623539639468446817437/100000000000000000000)
  centralHi := (311769819734223408719/50000000000000000000)
  directionLo := (625534971414648819703/100000000000000000000)
  directionHi := (78191871426831102463/12500000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree158.table
  base := (33561214703072083797034651057883626844373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-41311428647655062127020185158981313500000000000)
      constant := (1594208030267079964589343774710521796186836808954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree158.table
  base := (13424485881205573295267401837358101089373/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-18756868349948257023366952831976500000000000)
      constant := (725829878696966446708402211932728372466318265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625534971414648819703/100000000000000000000)
  centralHi := (78191871426831102463/12500000000000000000)
  directionLo := (313761979427483530101/50000000000000000000)
  directionHi := (627523958854967060203/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree159.table
  base := (17087030057575264410676019072307250301037/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-41573006619251436424016181136505371000000000000)
      constant := (1614757970508159981720830240897777553968746618452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree159.table
  base := (136696240460401254311274533250261970602949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-37751267933168959775444214917213000000000000)
      constant := (1470370628318922186216722448820951571387664589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313761979427483530101/50000000000000000000)
  centralHi := (627523958854967060203/100000000000000000000)
  directionLo := (629506661927652095109/100000000000000000000)
  directionHi := (62950666192765209511/10000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree160.table
  base := (2174510397085339863137615236079048975057/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-41834584590847810721012177114029428500000000000)
      constant := (1635439840434713953829610850728087308835527346976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree160.table
  base := (69584332706644153461894464046099978467987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-18994399583220702752077262085236500000000000)
      constant := (744600805335779486203819923360882092226943307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629506661927652095109/100000000000000000000)
  centralHi := (62950666192765209511/10000000000000000000)
  directionLo := (126296627965370499623/20000000000000000000)
  directionHi := (157870784956713124529/25000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree161.table
  base := (14166213367117924678167213615155438482663/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-42096162562444185018008173091553486000000000000)
      constant := (1656253640046866284445865733037787013250305633435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree161.table
  base := (70831066835514741356828682900296625649849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-19113165199856925616432416711866500000000000)
      constant := (754076352225978048836959258187613581859595489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126296627965370499623/20000000000000000000)
  centralHi := (157870784956713124529/25000000000000000000)
  directionLo := (158363362705808832303/25000000000000000000)
  directionHi := (633453450823235329213/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree162.table
  base := (144176645234060595720115649745952537551631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-84715481068081118630008338138155087000000000000)
      constant := (3354398738689477961598665646076744299118010589319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree162.table
  base := (7208832261696564191857837783894749012083/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-19231930816493148480787571338496500000000000)
      constant := (763611954830112104646987211019763043933619630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158363362705808832303/25000000000000000000)
  centralHi := (633453450823235329213/100000000000000000000)
  directionLo := (127083530456806226623/20000000000000000000)
  directionHi := (158854413071007783279/25000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree163.table
  base := (146712200102405813706037243737365972298847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-85238637011273867224000330093203202000000000000)
      constant := (3396554056656903332960020810550442457618743241303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree163.table
  base := (36678050025573541313690701421121123100271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-19350696433129371345142725965126500000000000)
      constant := (773207613148235885754269647144178950878395662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127083530456806226623/20000000000000000000)
  centralHi := (158854413071007783279/25000000000000000000)
  directionLo := (39835987543282685961/6250000000000000000)
  directionHi := (637375800692522975377/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree164.table
  base := (149268798276508987886306013014280310807621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-85761792954466615817992322048251317000000000000)
      constant := (3438973233996243202476980572346396472573226558829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree164.table
  base := (149268798276412593746297493695206410746699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-38938924099531188418995761183513000000000000)
      constant := (1565726654360805086825128867134541514279558339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39835987543282685961/6250000000000000000)
  centralHi := (637375800692522975377/100000000000000000000)
  directionLo := (639327951666998247531/100000000000000000000)
  directionHi := (159831987916749561883/25000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree165.table
  base := (151846439756658341191799589026809517938019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-86284948897659364411984314003299432000000000000)
      constant := (3481656270707727413237550367786868275145155313531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree165.table
  base := (30369287951315024057747066948570815607809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-39176455332803634147706070436773000000000000)
      constant := (1585158193853328322146430940504915322172095245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639327951666998247531/100000000000000000000)
  centralHi := (159831987916749561883/25000000000000000000)
  directionLo := (320637079989590615647/50000000000000000000)
  directionHi := (128254831995836246259/20000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree166.table
  base := (77222562271568154233588542824985418785243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-43404052420426056502988152979173773500000000000)
      constant := (1762301583395790596313084381286188245724873245107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree166.table
  base := (154445124543064463182223180763985906427189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-39413986566076079876416379690033000000000000)
      constant := (1604709844774143538778798527948576912220215229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320637079989590615647/50000000000000000000)
  centralHi := (128254831995836246259/20000000000000000000)
  directionLo := (160803619893040926039/25000000000000000000)
  directionHi := (643214479572163704157/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree167.table
  base := (3926621315905490552007844879096394635197/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3987245000000000000000000000000000000000000000
      center := (62201022)
      previous := (31100511)
      next := (31100511)
      square := (276928427546606102213899713015985000000000000)
      linear := (-43665630392022430799984148956697831000000000000)
      constant := (1783906961124012610296432770328193910296364249060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree167.table
  base := (157064852636157599708954406721307049355081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-39651517799348525605126688943293000000000000)
      constant := (1624381607123350725521103437827062844817184241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160803619893040926039/25000000000000000000)
  centralHi := (643214479572163704157/100000000000000000000)
  directionLo := (645148963577850193053/100000000000000000000)
  directionHi := (322574481788925096527/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree168.table
  base := (159705624036179405009367725896575863553007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-87854416727237610193960289868443777000000000000)
      constant := (3611288537077275703885449827622146451814481879143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree168.table
  base := (79852812018062932225349273484315719176519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (125363706449346356819329883665000000000000)
      linear := (-19944524516310485666918499098276500000000000)
      constant := (822086740450523917078682236021049974622723359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell033.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645148963577850193053/100000000000000000000)
  centralHi := (322574481788925096527/50000000000000000000)
  directionLo := (647077664333933837311/100000000000000000000)
  directionHi := (631911781576107263/97656250000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree169.table
  base := (162367438743281269714188037504970104048339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (124402044)
      previous := (62201022)
      next := (62201022)
      square := (553856855093212204427799426031970000000000000)
      linear := (-88377572670430358787952281823491892000000000000)
      constant := (3655027011279544454894415875988839014378243887211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree169.table
  base := (32473487748647010536462684194181942311771/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (250727412898692713638659767330000000000000)
      linear := (-40126580265893417062547307449813000000000000)
      constant := (1664085466107330816781805303420535405872746655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell033.Kernel169
