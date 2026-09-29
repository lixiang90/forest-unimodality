import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell146.Parameters
import ForestUnimodality.BinomialMassData.Q95749_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95749_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q95749_180624.Batch100_149
import ForestUnimodality.BinomialMassData.Q47887_90312.Batch000_049
import ForestUnimodality.BinomialMassData.Q47887_90312.Batch050_099
import ForestUnimodality.BinomialMassData.Q47887_90312.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree000.table
  base := (335672500840491934016807109/6250000000000000000000000)
  polynomial :=
    { denominator := 451560000000000000000000000000000000000000000
      center := (2776721)
      previous := (0)
      next := (2461375)
      square := (64870576013114258959735283103600000000000000)
      linear := (-296680022861655381887224793473200000000000000)
      constant := (24252203916725206035940706902406400000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree000.table
  base := (335672500840491934016807109/6250000000000000000000000)
  polynomial :=
    { denominator := 225780000000000000000000000000000000000000000
      center := (1388723)
      previous := (0)
      next := (1230325)
      square := (32435288006557129479867641551800000000000000)
      linear := (-148340011430827690943612396736600000000000000)
      constant := (12126101958362603017970353451203200000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree001.table
  base := (321681930447407525646160253344141365523869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-4125632375920187253766842396254779350000000000000)
      constant := (165963752308729147159207254892392751843952808658996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree001.table
  base := (321625925134152329761324646915649027850027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-2062917548235114117913045784507239050000000000000)
      constant := (82967886869240276095965037413404304769632601542134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (4990847280354660427/10000000000000000000)
  directionHi := (49908472803546604271/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree002.table
  base := (201538462350652790510041175107689094748533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-4902043973755146901408804098990603900000000000000)
      constant := (107111478113226507150674358304429384163214632154772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree002.table
  base := (100738090805918398875048675964670253742743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-2451224707427614432763651222255000700000000000000)
      constant := (53540543267855503589075286977134539139224442528412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4990847280354660427/10000000000000000000)
  centralHi := (49908472803546604271/100000000000000000000)
  directionLo := (35290619558052186777/50000000000000000000)
  directionHi := (14116247823220874711/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree003.table
  base := (5317980982917489124687210574332715729377/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-1892818523863368849683588600575476150000000000000)
      constant := (24983843891428282148633625043664027532393475413900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree003.table
  base := (132896462288454299009601511511559907040691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-946510622206704915871418886667587450000000000000)
      constant := (12487806716142642912495180817226700814547846620674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35290619558052186777/50000000000000000000)
  centralHi := (14116247823220874711/20000000000000000000)
  directionLo := (86444010623912245321/100000000000000000000)
  directionHi := (43222005311956122661/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree004.table
  base := (46237463674070041208387265837737354638153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-6454867169425066196692727504462253000000000000000)
      constant := (57534899246611911361749660399672088863820983605704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree004.table
  base := (92433504908925882170751672799154566019967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-3227839025812615062464862097750524000000000000000)
      constant := (28758678682559248466073238853333034865359021699614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86444010623912245321/100000000000000000000)
  centralHi := (43222005311956122661/50000000000000000000)
  directionLo := (4990847280354660427/5000000000000000000)
  directionHi := (99816945607093208541/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree005.table
  base := (2700299071837511932142557928359514661279/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-7231278767260025844334689207198077550000000000000)
      constant := (48434860975606398559254101401790364786457056535900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree005.table
  base := (33737949299727245884578297395400472920061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-3616146185005115377315467535498285650000000000000)
      constant := (24211884102824191187431613997520866864082541011124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4990847280354660427/5000000000000000000)
  centralHi := (99816945607093208541/100000000000000000000)
  directionLo := (111598737841929714307/100000000000000000000)
  directionHi := (27899684460482428577/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree006.table
  base := (12810148249855991486755025256175819952101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-2669230121698328497325550303311300700000000000000)
      constant := (14727217757197960701535541808389410834545459123312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree006.table
  base := (25608138299474007926190715546086977847571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-1334817781399205230722024324415349100000000000000)
      constant := (7362651353715304054973171642818429252750339193988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111598737841929714307/100000000000000000000)
  centralHi := (27899684460482428577/25000000000000000000)
  directionLo := (122250292210260611193/100000000000000000000)
  directionHi := (61125146105130305597/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree007.table
  base := (39978581103765308983555303947875888595781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-8784101962929945139618612612669726650000000000000)
      constant := (42891336240767054233051377497884962820929039291604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree007.table
  base := (39959298911882068789615452553023509704821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-4392760503390116007016678410993808950000000000000)
      constant := (21445009058240889603774814074082480597956298545482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122250292210260611193/100000000000000000000)
  centralHi := (61125146105130305597/50000000000000000000)
  directionLo := (132045407353214891427/100000000000000000000)
  directionHi := (33011351838303722857/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree008.table
  base := (31697731320766705518548630653809269670211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-9560513560764904787260574315405551200000000000000)
      constant := (43532291269245218228464787342947547582683432923724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree008.table
  base := (3168185366814272549688133957459737257591/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-4781067662582616321867283848741570600000000000000)
      constant := (21767392186348177392033266756066256247355316718220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132045407353214891427/100000000000000000000)
  centralHi := (33011351838303722857/25000000000000000000)
  directionLo := (141162478232208747109/100000000000000000000)
  directionHi := (14116247823220874711/10000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree009.table
  base := (12637861059528319953568862523820207889113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-3445641719533288144967512006047125250000000000000)
      constant := (15177465634997411137140212324954713021611860162328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree009.table
  base := (25262152423860292414859260180080502639279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-1723124940591705545572629762163110750000000000000)
      constant := (7589726198137940594562542249742374471487820068906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141162478232208747109/100000000000000000000)
  centralHi := (14116247823220874711/10000000000000000000)
  directionLo := (149725418410639812811/100000000000000000000)
  directionHi := (37431354602659953203/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree010.table
  base := (20078363987010289573129592267688747160983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-11113336756434824082544497720877200300000000000000)
      constant := (48568364844153241500058231774763706464870421500572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree010.table
  base := (5016600260514924134942177173906493101671/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-5557681980967616951568494724237093900000000000000)
      constant := (24288824904803851493362241267116717378723679052728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149725418410639812811/100000000000000000000)
  centralHi := (37431354602659953203/25000000000000000000)
  directionLo := (31564889719955310153/20000000000000000000)
  directionHi := (78912224299888275383/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree011.table
  base := (15737574369193882579225348415175203268667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-11889748354269783730186459423613024850000000000000)
      constant := (52452559083856055652551626159994995705109876490028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree011.table
  base := (3931696107006246637886848709171498002123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-5945989140160117266419100161984855550000000000000)
      constant := (26232581287283546722675718132522451863787130792664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31564889719955310153/20000000000000000000)
  centralHi := (78912224299888275383/50000000000000000000)
  directionLo := (165527678149020931347/100000000000000000000)
  directionHi := (41381919537255232837/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree012.table
  base := (1503973948901711112756965007720088860489/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-4222053317368247792609473708782949800000000000000)
      constant := (19024011665660167013578212376356114269115999613536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree012.table
  base := (12021911597964308651412079478117544473137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-2111432099784205860423235199910872400000000000000)
      constant := (9514672978144222360191643152871485339627815280918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165527678149020931347/100000000000000000000)
  centralHi := (41381919537255232837/25000000000000000000)
  directionLo := (86444010623912245321/50000000000000000000)
  directionHi := (172888021247824490643/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree013.table
  base := (8821330210409337837642561215364646474279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-13442571549939703025470382829084673950000000000000)
      constant := (62355585682429793948852001978020513301175112553436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree013.table
  base := (8812201412759905874976504667347767052353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-6722603458545117896120311037480378850000000000000)
      constant := (31187560980907053475760420155444266860086105897826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86444010623912245321/50000000000000000000)
  centralHi := (172888021247824490643/100000000000000000000)
  directionLo := (89973778886643640283/50000000000000000000)
  directionHi := (179947557773287280567/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree014.table
  base := (3006624773135083793698507920708878103303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-14218983147774662673112344531820498500000000000000)
      constant := (68255833133455719191588682840069370033258235550904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree014.table
  base := (1200954920276990074242788190480984968371/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-7110910617737618210970916475228140500000000000000)
      constant := (34139534075568645561952174596982335696973371322910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89973778886643640283/50000000000000000000)
  centralHi := (179947557773287280567/100000000000000000000)
  directionLo := (186740405927996511457/100000000000000000000)
  directionHi := (93370202963998255729/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree015.table
  base := (3542109649971132174096237585486761905479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-4998464915203207440251435411518774350000000000000)
      constant := (24913139427869524226671945377927261582944635991412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree015.table
  base := (883556522161821336747355173452441946107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-2499739258976706175273840637658634050000000000000)
      constant := (12461089191296742560391662504902210659694536289992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186740405927996511457/100000000000000000000)
  centralHi := (93370202963998255729/50000000000000000000)
  directionLo := (193294684002781788047/100000000000000000000)
  directionHi := (12080917750173861753/6250000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree016.table
  base := (169913166527351605684491102424651017199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-15771806343444581968396267937292147600000000000000)
      constant := (81781563855880169609819524724232777232833207029728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree016.table
  base := (675984866552286637085786840781555727407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-7887524936122618840672127350723663800000000000000)
      constant := (40906377692341934576667974693864384762588037864188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193294684002781788047/100000000000000000000)
  centralHi := (12080917750173861753/6250000000000000000)
  directionLo := (199633891214186417081/100000000000000000000)
  directionHi := (99816945607093208541/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree017.table
  base := (-143237050160069274949488318051324136293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-16548217941279541616038229640027972150000000000000)
      constant := (89363008443975024012314616029550804284546440453552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree017.table
  base := (-14494232922982889115911369435631322019/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-8275832095315119155522732788471425450000000000000)
      constant := (44699236261817455507274425489048785265007627928080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199633891214186417081/100000000000000000000)
  centralHi := (99816945607093208541/50000000000000000000)
  directionLo := (205777904982289018769/100000000000000000000)
  directionHi := (20577790498228901877/10000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree018.table
  base := (-91403646118311378329731559391778391231/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-5774876513038167087893397114254598900000000000000)
      constant := (32489411554708212380363015125177157012136276588300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree018.table
  base := (-1145713176539594047782510728962434035947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-2888046418169206490124446075406395700000000000000)
      constant := (16251361947531885356579855092320421185295660859484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205777904982289018769/100000000000000000000)
  centralHi := (20577790498228901877/10000000000000000000)
  directionLo := (211743717348313120663/100000000000000000000)
  directionHi := (26467964668539140083/12500000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree019.table
  base := (-1901148199427946226786577843122980131041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-18101041136949460911322153045499621250000000000000)
      constant := (106084410238864718716660101372763765362316345173112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree019.table
  base := (-1904085983756634699633776088313995083021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-9052446413700119785223943663966948750000000000000)
      constant := (53064510877583404171025753537721963036008129940236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211743717348313120663/100000000000000000000)
  centralHi := (26467964668539140083/12500000000000000000)
  directionLo := (217545989377107731283/100000000000000000000)
  directionHi := (54386497344276932821/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree020.table
  base := (-1286441360645886718172107742364223043303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-18877452734784420558964114748235445800000000000000)
      constant := (115200727360399374284111025154553189345051469058192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree020.table
  base := (-1030241329285870081190973189624165996963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-9440753572892620100074549101714710400000000000000)
      constant := (57625107722364179014740847019581707919905538992770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217545989377107731283/100000000000000000000)
  centralHi := (54386497344276932821/25000000000000000000)
  directionLo := (111598737841929714307/50000000000000000000)
  directionHi := (44639495136771885723/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree021.table
  base := (-6333579031110820842379499930156460653049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-6551288110873126735535358816990423450000000000000)
      constant := (41602656359049958266801415540599300318844209536628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree021.table
  base := (-1584652658397457323988063787297955221329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-3276353577361706804975051513154157350000000000000)
      constant := (20810422676469239675822756884001750707702174929576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111598737841929714307/50000000000000000000)
  centralHi := (44639495136771885723/20000000000000000000)
  directionLo := (228709354441897220699/100000000000000000000)
  directionHi := (2287093544418972207/1000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree022.table
  base := (-3690643339849457952848310963716294322553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-20430275930454339854248038153707094900000000000000)
      constant := (134898208773613419317804277645831299906151448615096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree022.table
  base := (-7385933067218235062151100480018225558971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-10217367891277620729775759977210233700000000000000)
      constant := (67479028587063132663524672946551324991587321130218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228709354441897220699/100000000000000000000)
  centralHi := (2287093544418972207/1000000000000000000)
  directionLo := (23409148738647401529/10000000000000000000)
  directionHi := (234091487386474015291/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree023.table
  base := (-20755843315909287503511400180945771647/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-21206687528289299501889999856442919450000000000000)
      constant := (145464590637323692460814593138323834051897731860800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree023.table
  base := (-1661324490080964090792598401446065581987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-10605675050470121044626365414957995350000000000000)
      constant := (72764961599952429901591164116980217074533265177730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23409148738647401529/10000000000000000000)
  centralHi := (234091487386474015291/100000000000000000000)
  directionLo := (7479769598488885803/3125000000000000000)
  directionHi := (239352627151644345697/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree024.table
  base := (-910840876338153788980616861347521783467/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-7327699708708086383177320519726248000000000000000)
      constant := (52167053908614076419764596145001425557791104889240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree024.table
  base := (-4556178005384558502890988870862310417937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-3664660736554207119825656950901919000000000000000)
      constant := (26095363580259272708522153859860193705018617383764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7479769598488885803/3125000000000000000)
  centralHi := (239352627151644345697/100000000000000000000)
  directionLo := (244500584420521222387/100000000000000000000)
  directionHi := (61125146105130305597/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree025.table
  base := (-1961933826097261513913284167655174753341/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-22759510723959218797173923261914568550000000000000)
      constant := (168002738666395302984254882875112354541705962566780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree025.table
  base := (-4906650590204339078308845557558562734177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-11382289368855121674327576290453518650000000000000)
      constant := (84039824503516944474158228497997226671205257747132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244500584420521222387/100000000000000000000)
  centralHi := (61125146105130305597/25000000000000000000)
  directionLo := (31192795502216627669/12500000000000000000)
  directionHi := (249542364017733021353/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree026.table
  base := (-10414990311039975577409020626989419999759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-23535922321794178444815884964650393100000000000000)
      constant := (179964798873743786846224451741658247451041573626244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree026.table
  base := (-2604582251755611578093507841534371045067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-11770596528047621989178181728201280300000000000000)
      constant := (90023901808546575406766880274601258279406415784744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31192795502216627669/12500000000000000000)
  centralHi := (249542364017733021353/100000000000000000000)
  directionLo := (254484276718898936347/100000000000000000000)
  directionHi := (63621069179724734087/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree027.table
  base := (-546606277634712417675689986047445488633/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-8104111306543046030819282222462072550000000000000)
      constant := (64127796668397996085758147317361234637353093845520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree027.table
  base := (-5467595900500621324721337675291985257003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-4052967895746707434676262388649680650000000000000)
      constant := (32078782241137256737691895909635272213608949037916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254484276718898936347/100000000000000000000)
  centralHi := (63621069179724734087/25000000000000000000)
  directionLo := (64833007967934183991/25000000000000000000)
  directionHi := (51866406374347347193/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree028.table
  base := (-11367859344498854824193672545886215836543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-25088745517464097740099808370122042200000000000000)
      constant := (205255053558331086021376794560956278318426690792388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree028.table
  base := (-2842668260403822051936788645813894481713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-12547210846432622618879392603696803600000000000000)
      constant := (102675430254280791014416537701036066284535908756216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64833007967934183991/25000000000000000000)
  centralHi := (51866406374347347193/20000000000000000000)
  directionLo := (52818162941285956571/20000000000000000000)
  directionHi := (33011351838303722857/12500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree029.table
  base := (-5864067533984841758256906790182122944849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-25865157115299057387741770072857866750000000000000)
      constant := (218576759798834007660308967561562215265133054597368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree029.table
  base := (-93845720443699543882551148611737838387/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-12935518005625122933729998041444565250000000000000)
      constant := (109339637802873817743801066699699813077552133343250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52818162941285956571/20000000000000000000)
  centralHi := (33011351838303722857/12500000000000000000)
  directionLo := (268765351319488688887/100000000000000000000)
  directionHi := (33595668914936086111/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree030.table
  base := (-12018164411800272384592056736638881059099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-8880522904378005678461243925197897100000000000000)
      constant := (77448617328188807085031647028629478208037110067228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree030.table
  base := (-3005132113745867735348642699484420911021/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-4441275054939207749526867826397442300000000000000)
      constant := (38742547090813755146165022039689667101287408258824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268765351319488688887/100000000000000000000)
  centralHi := (33595668914936086111/12500000000000000000)
  directionLo := (34169995456419467493/12500000000000000000)
  directionHi := (54671992730271147989/20000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree031.table
  base := (-765157598093598781058449047786350512929/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-27417980310968976683025693478329515850000000000000)
      constant := (246559998346816826054633724764094197034402176799424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree031.table
  base := (-122446863557663622028510402331140565963/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-13712132324010123563431208916940088550000000000000)
      constant := (123338275053370649556294197455943046018649890055400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34169995456419467493/12500000000000000000)
  centralHi := (54671992730271147989/20000000000000000000)
  directionLo := (277878616278858136989/100000000000000000000)
  directionHi := (27787861627885813699/10000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree032.table
  base := (-3101306147782864237513773829196481405639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-28194391908803936330667655181065340400000000000000)
      constant := (261217150619935799158525510470408122429074365809296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree032.table
  base := (-6203602871967392010109564319555595586349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-14100439483202623878281814354687850200000000000000)
      constant := (130670515284019098000187387471693521017659186412684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277878616278858136989/100000000000000000000)
  centralHi := (27787861627885813699/10000000000000000000)
  directionLo := (141162478232208747109/50000000000000000000)
  directionHi := (282324956464417494219/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree033.table
  base := (-12509805804581688044663170618920886495511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-9656934502212965326103205627933721650000000000000)
      constant := (92105169380990885960499936824474564427937457983692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree033.table
  base := (-625580895470617531013621828344749498257/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-4829582214131708064377473264145203950000000000000)
      constant := (46074487299489565342806701004199120336666880948040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141162478232208747109/50000000000000000000)
  centralHi := (282324956464417494219/100000000000000000000)
  directionLo := (5734046972260258159/2000000000000000000)
  directionHi := (286702348613012907951/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree034.table
  base := (-12559372885243585528547985866880483907909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-29747215104473855625951578586536989500000000000000)
      constant := (291853486728410791001927247135590495865990212441644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree034.table
  base := (-3140257381134660111682147182494884084497/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-14877053801587624507983025230183373500000000000000)
      constant := (145996323058623034630259970102659717917924078400504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5734046972260258159/2000000000000000000)
  centralHi := (286702348613012907951/100000000000000000000)
  directionLo := (291013904062675217649/100000000000000000000)
  directionHi := (5820278081253504353/2000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree035.table
  base := (-12556661894426339174055177519831626416143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-30523626702308815273593540289272814050000000000000)
      constant := (307829691624991028936346333864631389298429328505988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree035.table
  base := (-6279087844396554680100894569593425073761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-15265360960780124822833630667931135150000000000000)
      constant := (153988401634006617479448912435193674399876443878076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291013904062675217649/100000000000000000000)
  centralHi := (5820278081253504353/2000000000000000000)
  directionLo := (147631253479219540387/50000000000000000000)
  directionHi := (11810500278337563231/4000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree036.table
  base := (-12504083401157199401386098618526871681983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-10433346100047924973745167330669546200000000000000)
      constant := (108080964668793379516254557476486816616301677578476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree036.table
  base := (-12505466054821363148930332127507197356397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-5217889373324208379228078701892965600000000000000)
      constant := (54066361148340989741582648576571770170302391493442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147631253479219540387/50000000000000000000)
  centralHi := (11810500278337563231/4000000000000000000)
  directionLo := (149725418410639812811/50000000000000000000)
  directionHi := (299450836821279625623/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree037.table
  base := (-775235164680062593199373873750981555997/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-32076449897978734568877463694744463150000000000000)
      constant := (341092010502686424664137662439326073017628421508032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree037.table
  base := (-6202512491837630949866219565426302201261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-16041975279165125452534841543426658450000000000000)
      constant := (170627827028064885447470457605609760908137600168076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149725418410639812811/50000000000000000000)
  centralHi := (299450836821279625623/100000000000000000000)
  directionLo := (303581388313821024803/100000000000000000000)
  directionHi := (75895347078455256201/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree038.table
  base := (-12257574478140374914412229798707545562483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-32852861495813694216519425397480287700000000000000)
      constant := (358376085362378171094001474439779162331111463773428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree038.table
  base := (-2451745307742146196916193887029945825621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-16430282438357625767385446981174420100000000000000)
      constant := (179274154716163307160083024146642091251852589904590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303581388313821024803/100000000000000000000)
  centralHi := (75895347078455256201/25000000000000000000)
  directionLo := (307656488616979017439/100000000000000000000)
  directionHi := (1922853053856118859/625000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree039.table
  base := (-3016793498102063678654185550736736837187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-11209757697882884621387129033405370750000000000000)
      constant := (125364758297083180156403723219542139087904016579056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree039.table
  base := (-12068225011613304739325087682342322789857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-5606196532516708694078684139640727250000000000000)
      constant := (62712548286140356687889653538571612476283440365002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307656488616979017439/100000000000000000000)
  centralHi := (1922853053856118859/625000000000000000)
  directionLo := (31167831276126943699/10000000000000000000)
  directionHi := (311678312761269436991/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree040.table
  base := (-11834023072376764394774695317246752312709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-34405684691483613511803348802951936800000000000000)
      constant := (394245833864968108606012769278000629911832389638444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree040.table
  base := (-11834981576100213203120082980252510592027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-17206896756742626397086657856669943400000000000000)
      constant := (197217925026436236118034587814636830172166937293866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31167831276126943699/10000000000000000000)
  centralHi := (311678312761269436991/100000000000000000000)
  directionLo := (31564889719955310153/10000000000000000000)
  directionHi := (315648897199553101531/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree041.table
  base := (-5779706870457178386003118255557549673327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-35182096289318573159445310505687761350000000000000)
      constant := (412830103654095785864684167615844735306222731917064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree041.table
  base := (-1156028758170937507029259208468300653001/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-17595203915935126711937263294417705050000000000000)
      constant := (206514666077110295312021264425460062586800186909580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31564889719955310153/10000000000000000000)
  centralHi := (315648897199553101531/100000000000000000000)
  directionLo := (15978507593082370913/5000000000000000000)
  directionHi := (319570151861647418261/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree042.table
  base := (-11244488526080798952140057135309633475643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-11986169295717844269029090736141195300000000000000)
      constant := (143948833945525894883245019702479446103132052835996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree042.table
  base := (-17570757701913042776791070088484682927/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-5994503691709209008929289577388488900000000000000)
      constant := (72009192319765957481545135546083352846134298894080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15978507593082370913/5000000000000000000)
  centralHi := (319570151861647418261/100000000000000000000)
  directionLo := (8086096772333157957/2500000000000000000)
  directionHi := (323443870893326318281/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree043.table
  base := (-5445129150528163666625243879496005377631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-36734919484988492454729233911159410450000000000000)
      constant := (451294513103551295226324827117618410350941707865992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree043.table
  base := (-10890983908718607334957551950261060194723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-18371818234320127341638474169913228350000000000000)
      constant := (225756400167191737240749211300292368705298889412634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8086096772333157957/2500000000000000000)
  centralHi := (323443870893326318281/100000000000000000000)
  directionLo := (10227241945345474313/3125000000000000000)
  directionHi := (327271742251055178017/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree044.table
  base := (-2624404478998442421339260050196747564581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-37511331082823452102371195613895235000000000000000)
      constant := (471173681290758443780604172503012889732868026116784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree044.table
  base := (-262456970733208973289623384959042335277/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-18760125393512627656489079607660990000000000000000)
      constant := (235700907756558765635604762152585608817112573094640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10227241945345474313/3125000000000000000)
  centralHi := (327271742251055178017/100000000000000000000)
  directionLo := (66211071259608372539/20000000000000000000)
  directionHi := (41381919537255232837/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree045.table
  base := (-10067359906320976329779280598204837242847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-12762580893552803916671052438877019850000000000000)
      constant := (163827867463505881263245292773708054341598009266284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree045.table
  base := (-40271846901439417406251787096568664007/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-6382810850901709323779895015136250550000000000000)
      constant := (81953632617095203904262919177121930236959994225500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66211071259608372539/20000000000000000000)
  centralHi := (41381919537255232837/12500000000000000000)
  directionLo := (334796213525789142921/100000000000000000000)
  directionHi := (167398106762894571461/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree046.table
  base := (-9600186523806630926704688422063617153869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-39064154278493371397655119019366884100000000000000)
      constant := (512223918418694791310431386456282912728346974421004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree046.table
  base := (-9600734385105312849424988873541140300973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-19536739711897628286190290483156513300000000000000)
      constant := (256236191577437514643774751441392762885439206200134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334796213525789142921/100000000000000000000)
  centralHi := (167398106762894571461/50000000000000000000)
  directionLo := (338495731507486144393/100000000000000000000)
  directionHi := (169247865753743072197/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree047.table
  base := (-1819344060766610866192132374477934233693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-39840565876328331045297080722102708650000000000000)
      constant := (533394312027865889197693801632153062204841392658940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree047.table
  base := (-9097218915857835041467487840410833776919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-19925046871090128601040895920904274950000000000000)
      constant := (266826630370415158557869036013393142554057535892402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338495731507486144393/100000000000000000000)
  centralHi := (169247865753743072197/50000000000000000000)
  directionLo := (342155251174624673683/100000000000000000000)
  directionHi := (85538812793656168421/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree048.table
  base := (-1711502670803307955633305567324620728209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-13538992491387763564313014141612844400000000000000)
      constant := (184998167257431144358068590088869453557659449560740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree048.table
  base := (-1069745878787651430479524933348426731669/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-6771118010094209638630500452884012200000000000000)
      constant := (92544024536003796314741876965234543996581566781072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342155251174624673683/100000000000000000000)
  centralHi := (85538812793656168421/25000000000000000000)
  directionLo := (69155208499129796257/20000000000000000000)
  directionHi := (172888021247824490643/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree049.table
  base := (-997881940614952982328629816929992985237/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-41393389071998250340581004127574357750000000000000)
      constant := (577024237942774413465219906921356484838583617584736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree049.table
  base := (-249483381720164368454435198770597511077/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-20701661189475129230742106796399798250000000000000)
      constant := (288652396528390077191734315858738655125885097400512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69155208499129796257/20000000000000000000)
  centralHi := (172888021247824490643/50000000000000000000)
  directionLo := (349359309624826229893/100000000000000000000)
  directionHi := (174679654812413114947/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree050.table
  base := (-737378160255037049847414259752803416369/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-42169800669833209988222965830310182300000000000000)
      constant := (599483298900148121630693321473166063287907533710040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree050.table
  base := (-7374156921020735967939094152757073028887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-21089968348667629545592712234147559900000000000000)
      constant := (299887488397376392508721668607574695476881127565746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349359309624826229893/100000000000000000000)
  centralHi := (174679654812413114947/50000000000000000000)
  directionLo := (352906195580521867773/100000000000000000000)
  directionHi := (176453097790260933887/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree051.table
  base := (-6730077644164502237401685981474551264033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-14315404089222723211954975844348668950000000000000)
      constant := (207457162615173036034990896304108294914138049181076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree051.table
  base := (-6730418897262874242870827769568990293031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-7159425169286709953481105890631773850000000000000)
      constant := (103779083631360928606690691241387512332372929106566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352906195580521867773/100000000000000000000)
  centralHi := (176453097790260933887/50000000000000000000)
  directionLo := (356417786504405393321/100000000000000000000)
  directionHi := (178208893252202696661/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree052.table
  base := (-75653582039633817834399866042977989009/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-43722623865503129283506889235781831400000000000000)
      constant := (645688629973261875755151005857224560862574962339520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree052.table
  base := (-1513149193473146387518858666515048382013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-21866582667052630175293923109643083200000000000000)
      constant := (323001596687901758518928367930449340568461393905816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356417786504405393321/100000000000000000000)
  centralHi := (178208893252202696661/50000000000000000000)
  directionLo := (89973778886643640283/25000000000000000000)
  directionHi := (359895115546574561133/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree053.table
  base := (-2670356527670434684370295344248202140469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96182280000000000000000000000000000000000000000
      center := (591441573)
      previous := (0)
      next := (524272875)
      square := (13817432690793337158423615301066800000000000000)
      linear := (-839604442704492243983940583745616150000000000000)
      constant := (12630840942637848626685969148741618223633262262136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree053.table
  base := (-2670497493251123458054759541353780543049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48091140000000000000000000000000000000000000000
      center := (295797999)
      previous := (0)
      next := (262059225)
      square := (6908716345396668579211807650533400000000000000)
      linear := (-419903581627266613021594878252657450000000000000)
      constant := (6318499022327611933523601682121363394449990902828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89973778886643640283/25000000000000000000)
  centralHi := (359895115546574561133/100000000000000000000)
  directionLo := (14533566656639497061/4000000000000000000)
  directionHi := (181669583207993713263/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree054.table
  base := (-1148906986687277504974095480806549561991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-15091815687057682859596937547084493500000000000000)
      constant := (231203056582401388432555706207417088822225910249008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree054.table
  base := (-2297942061186186741736005550742824816733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-7547732328479210268331711328379535500000000000000)
      constant := (115657912137452874495564148869690770213192000305476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14533566656639497061/4000000000000000000)
  centralHi := (181669583207993713263/50000000000000000000)
  directionLo := (366750876630781833581/100000000000000000000)
  directionHi := (183375438315390916791/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree055.table
  base := (-3817272033652802310600615532196794499847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-46051858659008008226432774343989305050000000000000)
      constant := (718212306585691276130703043337400999673897756210852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree055.table
  base := (-3817504758732745312464642513907110209319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-23031504144630131119845739422886368150000000000000)
      constant := (359281400055831169273992391463480638491294516531602) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366750876630781833581/100000000000000000000)
  centralHi := (183375438315390916791/50000000000000000000)
  directionLo := (185065570249458683249/50000000000000000000)
  directionHi := (370131140498917366499/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree056.table
  base := (-150292973783431302834320474564412961879/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-46828270256842967874074736046725129600000000000000)
      constant := (743243871303958163902665049280680577673282017763280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree056.table
  base := (-3006070854419760989410316531041487123079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-23419811303822631434696344860634129800000000000000)
      constant := (371803384579301985786644242550948269933865796073682) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185065570249458683249/50000000000000000000)
  centralHi := (370131140498917366499/100000000000000000000)
  directionLo := (74696162371198604583/20000000000000000000)
  directionHi := (93370202963998255729/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree057.table
  base := (-2161580795901022676900457292270685268383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-15868227284892642507238899249820318050000000000000)
      constant := (256234588926595988662837076774280691342059136359276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree057.table
  base := (-432354549717001836729607698246437588323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-7936039487671710583182316766127297150000000000000)
      constant := (128179880489516368135158047353861332668666816802390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74696162371198604583/20000000000000000000)
  centralHi := (93370202963998255729/25000000000000000000)
  directionLo := (376800706583989846949/100000000000000000000)
  directionHi := (7536014131679796939/2000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree058.table
  base := (-1284605534990155824406372613404527088783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-48381093452512887169358659452196778700000000000000)
      constant := (794591906587112467309649236907829820911829169764228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree058.table
  base := (-321194953354724015840981979535997858901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-24196425622207632064397555736129653100000000000000)
      constant := (397490127553473404203119248229020552906371305372632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376800706583989846949/100000000000000000000)
  centralHi := (7536014131679796939/2000000000000000000)
  directionLo := (95022901232997630149/25000000000000000000)
  directionHi := (380091604931990520597/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree059.table
  base := (-75016920044951197399116922381704375979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-49157505050347846817000621154932603250000000000000)
      constant := (820908213798514044667986222385405002345995107518820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree059.table
  base := (-75048560406172088608226595024435922023/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-24584732781400132379248161173877414750000000000000)
      constant := (410654804409663760455631222591647776261178514830170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95022901232997630149/25000000000000000000)
  centralHi := (380091604931990520597/100000000000000000000)
  directionLo := (15334170146303122937/4000000000000000000)
  directionHi := (191677126828789036713/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree060.table
  base := (283423827102658076120287250730522187959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-16644638882727602154880860952556142600000000000000)
      constant := (282550873308261154596865717773382441248353980921704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree060.table
  base := (141676018110807079196405058954491636123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-8324346646864210898032922203875058800000000000000)
      constant := (141344545942822608807027459804649070307038116434888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15334170146303122937/4000000000000000000)
  centralHi := (191677126828789036713/50000000000000000000)
  directionLo := (193294684002781788047/50000000000000000000)
  directionHi := (77317873601112715219/20000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree061.table
  base := (385267896040568344183980972813069552211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-50710328246017766112284544560404252350000000000000)
      constant := (874825063975397131331667827780732625004538440046896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree061.table
  base := (1540941294856449497832470128582790505863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-25361347099785133008949372049372938050000000000000)
      constant := (437626597347501389869863703035348360814858080275246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193294684002781788047/50000000000000000000)
  centralHi := (77317873601112715219/20000000000000000000)
  directionLo := (194898816769447970511/50000000000000000000)
  directionHi := (389797633538895941023/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree062.table
  base := (1273740310960903177869300610246585567379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-51486739843852725759926506263140076900000000000000)
      constant := (902425491625743545332056208127935596941857421947672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree062.table
  base := (50947248307920150259702861222025811147/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-25749654258977633323799977487120699700000000000000)
      constant := (451433655834512345132207331388339749844883243458700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194898816769447970511/50000000000000000000)
  centralHi := (389797633538895941023/100000000000000000000)
  directionLo := (196489853917515143553/50000000000000000000)
  directionHi := (392979707835030287107/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree063.table
  base := (3585979827513492272333563150799721628697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-17421050480562561802522822655291967150000000000000)
      constant := (310151284826215256092186421252819313403796157237516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree063.table
  base := (896468150458403648459315275840650526933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-8712653806056711212883527641622820450000000000000)
      constant := (155151596372791288861083485124639515250376447960248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196489853917515143553/50000000000000000000)
  centralHi := (392979707835030287107/100000000000000000000)
  directionLo := (198068111029822337141/50000000000000000000)
  directionHi := (396136222059644674283/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree064.table
  base := (2328242301777635542776005654266101307639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-53039563039522645055210429668611726000000000000000)
      constant := (958910109409227630766239450759183762315084824631352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree064.table
  base := (582048419400087098986188150824601819491/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-26526268577362633953501188362616223000000000000000)
      constant := (479689975661731798232597617218005727361524807772976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198068111029822337141/50000000000000000000)
  centralHi := (396136222059644674283/100000000000000000000)
  directionLo := (399267782428372834163/100000000000000000000)
  directionHi := (99816945607093208541/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree065.table
  base := (1151783910934564328095588478018213476719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-53815974637357604702852391371347550550000000000000)
      constant := (987794217983484413391796880777106059221952848991980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree065.table
  base := (1151766273996740966494798996862960436663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-26914575736555134268351793800363984650000000000000)
      constant := (494139196270487767268904574028000810612986568844230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399267782428372834163/100000000000000000000)
  centralHi := (99816945607093208541/25000000000000000000)
  directionLo := (100593742891535262341/25000000000000000000)
  directionHi := (80474994313228209873/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree066.table
  base := (1378643494969994970568776228575278562331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-18197462078397521450164784358027791700000000000000)
      constant := (339035381980689477466154218981380019101131039636340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree066.table
  base := (861642190273746724440799697496363566703/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-9100960965249211527734133079370582100000000000000)
      constant := (169600811278624777357219547269908962992017948134736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100593742891535262341/25000000000000000000)
  centralHi := (80474994313228209873/20000000000000000000)
  directionLo := (405458349772741970851/100000000000000000000)
  directionHi := (101364587443185492713/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree067.table
  base := (1611863689606530603963392930279809790893/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-55368797833027523998136314776819199650000000000000)
      constant := (1046845862741807431863431955025348039842779417365060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree067.table
  base := (1611849194122151603850018430488461866659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-27691190054940134898053004675859507950000000000000)
      constant := (523679673105382170589576794657877978304250221483390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405458349772741970851/100000000000000000000)
  centralHi := (101364587443185492713/25000000000000000000)
  directionLo := (40851845620243098149/10000000000000000000)
  directionHi := (408518456202430981491/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree068.table
  base := (9257169049042134260878553792172163773141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-56145209430862483645778276479555024200000000000000)
      constant := (1077013341148357267733547672465740911655440751949844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree068.table
  base := (9257103358341190308165516485908891434419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-28079497214132635212903610113607269600000000000000)
      constant := (538770900479241058567269193106057587633652458222598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40851845620243098149/10000000000000000000)
  centralHi := (408518456202430981491/100000000000000000000)
  directionLo := (411555809964578037539/100000000000000000000)
  directionHi := (20577790498228901877/5000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree069.table
  base := (1048672163337480542865815724901395118671/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-18973873676232481097806746060763616250000000000000)
      constant := (369202852291388636336941279669970892606251269847880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree069.table
  base := (2621665525784520185700577922488865263053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-9489268124441711842584738517118343750000000000000)
      constant := (184692034609848035524759165683814982576458438462968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411555809964578037539/100000000000000000000)
  centralHi := (20577790498228901877/5000000000000000000)
  directionLo := (207285455575868987537/50000000000000000000)
  directionHi := (16582836446069519003/4000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree070.table
  base := (2936983426450484377157125266974493772183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-57698032626532402941062199885026673300000000000000)
      constant := (1138631488256607017821227707103124085966262464165488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree070.table
  base := (11747879766532637534796195232148130769283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-28856111532517635842604820989102792900000000000000)
      constant := (569595272339445291137518797958025845702588651198886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207285455575868987537/50000000000000000000)
  centralHi := (16582836446069519003/4000000000000000000)
  directionLo := (13048882556278278057/3125000000000000000)
  directionHi := (16702569672036195913/4000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree071.table
  base := (6520383679428888183160021814845342701139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71798040000000000000000000000000000000000000000
      center := (441498639)
      previous := (0)
      next := (391358625)
      square := (10314421586085167174597910013472400000000000000)
      linear := (-823583721469962853362030444898063350000000000000)
      constant := (16480029802418876370641182099956540940876517193512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree071.table
  base := (6520359246394873224409129685134204207697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35899020000000000000000000000000000000000000000
      center := (220806957)
      previous := (0)
      next := (195621675)
      square := (5157210793042583587298955006736200000000000000)
      linear := (-411893221010001917710639808828881050000000000000)
      constant := (8244061920565629425274295210562341978032239751388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13048882556278278057/3125000000000000000)
  centralHi := (16702569672036195913/4000000000000000000)
  directionLo := (420536266793182683089/100000000000000000000)
  directionHi := (42053626679318268309/10000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree072.table
  base := (1436518877333769222546947766723867145563/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-19750285274067440745448707763499440800000000000000)
      constant := (400653474259894004792665654230939368113766361617640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree072.table
  base := (14365144509838693021939426724757897242309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-9877575283634212157435343954866105400000000000000)
      constant := (200425155761253060801240407851463673054214376341326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420536266793182683089/100000000000000000000)
  centralHi := (42053626679318268309/10000000000000000000)
  directionLo := (423487434696626241327/100000000000000000000)
  directionHi := (26467964668539140083/6250000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree073.table
  base := (3930291943459480094546138952258672056229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-60027267420037281883988084993234146950000000000000)
      constant := (1234266393298034983754647173054302637110013840548944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree073.table
  base := (3930281921302450608098806102488878881741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-30021033010095136787156637302346077850000000000000)
      constant := (617436477429988237073935452114796247179065817344488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423487434696626241327/100000000000000000000)
  centralHi := (26467964668539140083/6250000000000000000)
  directionLo := (26651136159786270739/6250000000000000000)
  directionHi := (17056727142263213273/4000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree074.table
  base := (17108677433169905442377632721627850479049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-60803679017872241531630046695969971500000000000000)
      constant := (1267000013800231667438730617474953873137792332774116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree074.table
  base := (213858014135159490509950475440417359/125000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-30409340169287637102007242740093839500000000000000)
      constant := (633811419945528600035186454092051755534422086240000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26651136159786270739/6250000000000000000)
  centralHi := (17056727142263213273/4000000000000000000)
  directionLo := (85865783327491743641/20000000000000000000)
  directionHi := (214664458318729359103/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree075.table
  base := (18527693720188799996677410801099788639309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-20526696871902400393090669466235265350000000000000)
      constant := (433387090678669820841159117221741254036275245798652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree075.table
  base := (9263830425549361289886529716951603033941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-10265882442826712472285949392613867050000000000000)
      constant := (216800096238107262755875116374905861506003207552348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85865783327491743641/20000000000000000000)
  centralHi := (214664458318729359103/50000000000000000000)
  directionLo := (216110026559780613303/50000000000000000000)
  directionHi := (432220053119561226607/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree076.table
  base := (9989097593099458293733668827240059959403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-62356502213542160826913970101441620600000000000000)
      constant := (1333750157071550761507969334074166962861860132575704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree076.table
  base := (19978165429771423480383301400707617402819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-31185954487672637731708453615589362800000000000000)
      constant := (667203078277717060363197745109350662326202646095398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216110026559780613303/50000000000000000000)
  centralHi := (432220053119561226607/100000000000000000000)
  directionLo := (217545989377107731283/50000000000000000000)
  directionHi := (435091978754215462567/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree077.table
  base := (4292032537129810705208722957356223742261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-63132913811377120474555931804177445150000000000000)
      constant := (1367766659147102902285861842307068488886538576379620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree077.table
  base := (2146013575076238402072761154476406966191/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-31574261646865138046559059053337124450000000000000)
      constant := (684219783763352731588860147667341270769602532330220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217545989377107731283/50000000000000000000)
  centralHi := (435091978754215462567/100000000000000000000)
  directionLo := (87589014296049942591/20000000000000000000)
  directionHi := (109486267870062428239/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree078.table
  base := (574339478182912090660559370282822690493/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-21303108469737360040732631168971089900000000000000)
      constant := (467403589850046734815918513533013375886569475192160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree078.table
  base := (11486777374835553593444030836514133035311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-10654189602019212787136554830361628700000000000000)
      constant := (233816800273934164453131079640836238748521840730708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87589014296049942591/20000000000000000000)
  centralHi := (109486267870062428239/25000000000000000000)
  directionLo := (440779697004550541437/100000000000000000000)
  directionHi := (220389848502275270719/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree079.table
  base := (4903685850521553200552036494937632359447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-64685737007047039769839855209649094250000000000000)
      constant := (1437082480502349242285188529923855074858972387977740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree079.table
  base := (4903681438460061351934498631182689968623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-32350875965250138676260269928832647750000000000000)
      constant := (718894925570127798935104642700797374981602573955830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440779697004550541437/100000000000000000000)
  centralHi := (220389848502275270719/50000000000000000000)
  directionLo := (221798104674614911709/50000000000000000000)
  directionHi := (443596209349229823419/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree080.table
  base := (3261837429748024632104641932122745175661/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-65462148604881999417481816912384918800000000000000)
      constant := (1472381785058912040642459541305022688924212800652192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree080.table
  base := (3261834934661970116377210895297771988859/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-32739183124442638991110875366580409400000000000000)
      constant := (736553354541574108942012465658240738962742176232624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221798104674614911709/50000000000000000000)
  centralHi := (443596209349229823419/100000000000000000000)
  directionLo := (111598737841929714307/25000000000000000000)
  directionHi := (446394951367718857229/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree081.table
  base := (27702377518855595437613675264139185783741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-22079520067572319688374592871706914450000000000000)
      constant := (502702892339577699769133103226646517905454540146748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree081.table
  base := (1108094378409444765662234831878280536671/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-11042496761211713101987160268109390350000000000000)
      constant := (251475228213578122073265549414158124189925808609850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111598737841929714307/25000000000000000000)
  centralHi := (446394951367718857229/100000000000000000000)
  directionLo := (224588127615959719217/50000000000000000000)
  directionHi := (89835251046383887687/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree082.table
  base := (29341452632583419095774224845453427883201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-67014971800551918712765740317856567900000000000000)
      constant := (1544263150844407706792058898455266794680145783154884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree082.table
  base := (1833839768550948163678807370917775458001/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-33515797442827639620812086242075932700000000000000)
      constant := (772511913103578815387288049706494441587231809904672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224588127615959719217/50000000000000000000)
  centralHi := (89835251046383887687/20000000000000000000)
  directionLo := (451940442892371367971/100000000000000000000)
  directionHi := (112985110723092841993/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree083.table
  base := (31011915078497501934811967670091653644559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-67791383398386878360407702020592392450000000000000)
      constant := (1580845201590863220349792461688775190785408669336956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree083.table
  base := (7752975075755564082372802606401267020729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-33904104602020139935662691679823694350000000000000)
      constant := (790812037461817360909618290686836910115465738310472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451940442892371367971/100000000000000000000)
  centralHi := (112985110723092841993/25000000000000000000)
  directionLo := (227343913256620495331/50000000000000000000)
  directionHi := (454687826513240990663/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree084.table
  base := (32713756193063975733450524035798050469917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-22855931665407279336016554574442739000000000000000)
      constant := (539284941613907968792022631272649570159294649631676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree084.table
  base := (32713742830459675951644408857357974351791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-11430803920404213416837765705857152000000000000000)
      constant := (269775351837040029500987337330454236211914156076074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227343913256620495331/50000000000000000000)
  centralHi := (454687826513240990663/100000000000000000000)
  directionLo := (228709354441897220699/50000000000000000000)
  directionHi := (457418708883794441399/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree085.table
  base := (34446968238548725296059053271472402483239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-69344206594056797655691625426064041550000000000000)
      constant := (1655292016652555345934403567284252664738890120666076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree085.table
  base := (34446956155142622975512305256815293527697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-34680718920405140565363902555319217650000000000000)
      constant := (828053965282774254322317894735312360918337322614274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228709354441897220699/50000000000000000000)
  centralHi := (457418708883794441399/100000000000000000000)
  directionLo := (57516672975986362961/12500000000000000000)
  directionHi := (460133383807890903689/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree086.table
  base := (36211544303704100758163150319393797900119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-70120618191891757303333587128799866100000000000000)
      constant := (1693156773500237888999183233903182870403181085763996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree086.table
  base := (724230667566209266868904652770313997289/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-35069026079597640880214507993066979300000000000000)
      constant := (846995765018402761929223388427144514483710003656900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57516672975986362961/12500000000000000000)
  centralHi := (460133383807890903689/100000000000000000000)
  directionLo := (28927008529557131763/6250000000000000000)
  directionHi := (462832136472914108209/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree087.table
  base := (2375467388448081128152083215782867193093/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-23632343263242238983658516277178563550000000000000)
      constant := (577149697412600524453631179416488758825492982441664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree087.table
  base := (950186708448519329537450801292437756779/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-11819111079596713731688371143604913650000000000000)
      constant := (288717151049136863684824642137438501109538168556240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28927008529557131763/6250000000000000000)
  centralHi := (462832136472914108209/100000000000000000000)
  directionLo := (465515243799453404067/100000000000000000000)
  directionHi := (116378810949863351017/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree088.table
  base := (9958691114604802127865176918624112920313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-71673441387561676598617510534271515200000000000000)
      constant := (1770168970054128529257533589056631545345447048257168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree088.table
  base := (19917377764900930282923482388359704012863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-35845640397982641509915718868562502600000000000000)
      constant := (885521028266862424187718481894149963498036257138492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465515243799453404067/100000000000000000000)
  centralHi := (116378810949863351017/25000000000000000000)
  directionLo := (468182974772948030581/100000000000000000000)
  directionHi := (234091487386474015291/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree089.table
  base := (41693398107224738216515487956635403363429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-72449852985396636246259472237007339750000000000000)
      constant := (1809316404437994242592225689993855176011773130142036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree089.table
  base := (5211673754625952651268176009341266872717/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-36233947557175141824766324306310264250000000000000)
      constant := (905104489123527373900923788602543114730090486120912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468182974772948030581/100000000000000000000)
  centralHi := (234091487386474015291/50000000000000000000)
  directionLo := (117708897689604704287/25000000000000000000)
  directionHi := (470835590758418817149/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree090.table
  base := (43583374760701463555945141858095224092269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-24408754861077198631300477979914388100000000000000)
      constant := (616297131048659031534960042005871847226122807601532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree090.table
  base := (348666939737218999048172298958523811163/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-12207418238789214046538976581352675300000000000000)
      constant := (308300611532618572906042921990831860679944124910250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117708897689604704287/25000000000000000000)
  centralHi := (470835590758418817149/100000000000000000000)
  directionLo := (94694669159865930459/20000000000000000000)
  directionHi := (59184168224916206537/12500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree091.table
  base := (2275234524356232979202909822164173737027/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-74002676181066555541543395642478988850000000000000)
      constant := (1888893934173817168893954642297343700431335491845360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree091.table
  base := (4550468389620443552011139054120790866707/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-37010561875560142454467535181805787550000000000000)
      constant := (944913063689678325592388617795493367637395966826940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94694669159865930459/20000000000000000000)
  centralHi := (59184168224916206537/12500000000000000000)
  directionLo := (476096486901545982353/100000000000000000000)
  directionHi := (238048243450772991177/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree092.table
  base := (11864335443444664228556380236505569719273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-74779087778901515189185357345214813400000000000000)
      constant := (1929324025730851154470788624882041236554931106147728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree092.table
  base := (23728667909213514186767283313422674344453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-37398869034752642769318140619553549200000000000000)
      constant := (965138175505442340923165506170146361187379072932052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476096486901545982353/100000000000000000000)
  centralHi := (238048243450772991177/50000000000000000000)
  directionLo := (478705254303288691393/100000000000000000000)
  directionHi := (239352627151644345697/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree093.table
  base := (49441325482188427701664894933503787838759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-25185166458912158278942439682650212650000000000000)
      constant := (656727222072396975553052160476283635970556166283252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree093.table
  base := (49441320101675057816224507945578235640921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-12595725397981714361389582019100436950000000000000)
      constant := (328525723082272364917387191807404898857008588053894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478705254303288691393/100000000000000000000)
  centralHi := (239352627151644345697/50000000000000000000)
  directionLo := (481299881731918408369/100000000000000000000)
  directionHi := (48129988173191840837/10000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree094.table
  base := (51456638808152399198358385859140983470707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-76331910974571434484469280750686462500000000000000)
      constant := (2011466854203349630972659991701722902691521036101388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree094.table
  base := (6432079243435909670115174051472581349113/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-38175483353137643399019351495049072500000000000000)
      constant := (1006230044200522271655592227854135255148335083533968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481299881731918408369/100000000000000000000)
  centralHi := (48129988173191840837/10000000000000000000)
  directionLo := (241940298324163536959/50000000000000000000)
  directionHi := (483880596648327073919/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree095.table
  base := (26751639623029370718388525270734115647139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-77108322572406394132111242453422287050000000000000)
      constant := (2053179588412051336824678079178382983025727847667352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree095.table
  base := (6687909356932076901722254215482064170363/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-38563790512330143713869956932796834150000000000000)
      constant := (1027096799729246510936329295738216498394325621473968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241940298324163536959/50000000000000000000)
  centralHi := (483880596648327073919/100000000000000000000)
  directionLo := (486447620479660018787/100000000000000000000)
  directionHi := (121611905119915004697/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree096.table
  base := (1389531113925591391777989826059353609099/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-25961578056747117926584401385386037200000000000000)
      constant := (698439955900663005865839835262111666945088853310880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree096.table
  base := (55581240591417646269294796141694757250453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-12984032557174214676240187456848198600000000000000)
      constant := (349392478421179644237419953662375665454482338839342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486447620479660018787/100000000000000000000)
  centralHi := (121611905119915004697/25000000000000000000)
  directionLo := (244500584420521222387/50000000000000000000)
  directionHi := (19560046753641697791/4000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree097.table
  base := (57690532740440282759105719217510997367081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-78661145768076313427395165858893936150000000000000)
      constant := (2137887691053321149082684447149246685453188691880804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree097.table
  base := (2884526457952012742189801960680088385317/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-39340404830715144343571167808292357450000000000000)
      constant := (1069471950294568844261716766621240826476444301886280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244500584420521222387/50000000000000000000)
  centralHi := (19560046753641697791/4000000000000000000)
  directionLo := (49154145174693868479/10000000000000000000)
  directionHi := (491541451746938684791/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree098.table
  base := (11966228401714289360534178840838664438167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-79437557365911273075037127561629760700000000000000)
      constant := (2180883057554719951901397362150885388075922258640140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree098.table
  base := (14957784693615773144538363394367661626409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-39728711989907644658421773246040119100000000000000)
      constant := (1090980344367660238608703680682027102984563173824712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49154145174693868479/10000000000000000000)
  centralHi := (491541451746938684791/100000000000000000000)
  directionLo := (247034336906365307441/50000000000000000000)
  directionHi := (494068673812730614883/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree099.table
  base := (62003070763859161328992372323563241081481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-26737989654582077574226363088121861750000000000000)
      constant := (741435322130601515775494142433470602256130664763468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree099.table
  base := (62003067843640114809887153608825682502687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-13372339716366714991090792894595960250000000000000)
      constant := (370900872358839270267193288885902462325295345244618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247034336906365307441/50000000000000000000)
  centralHi := (494068673812730614883/100000000000000000000)
  directionLo := (496583034447062794043/100000000000000000000)
  directionHi := (124145758611765698511/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree100.table
  base := (32103158789329597863292985933997715765227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-80990380561581192370321050967101409800000000000000)
      constant := (2268156416836810326573930425860785347936169662322136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree100.table
  base := (32103157471054409372854524381513599177227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-40505326308292645288122984121535642400000000000000)
      constant := (1134638768058070224913458558847892480695320629769068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496583034447062794043/100000000000000000000)
  centralHi := (124145758611765698511/25000000000000000000)
  directionLo := (31192795502216627669/6250000000000000000)
  directionHi := (99816945607093208541/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree101.table
  base := (33220440588570254859384952057867766589393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-81766792159416152017963012669837234350000000000000)
      constant := (2312434408239361896396251005881201925689139311094024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree101.table
  base := (13288175759384057783510498590178688116221/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-40893633467485145602973589559283404050000000000000)
      constant := (1156788796987864389059238076638634335525033290121410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31192795502216627669/6250000000000000000)
  centralHi := (99816945607093208541/20000000000000000000)
  directionLo := (250786972057868994679/50000000000000000000)
  directionHi := (501573944115737989359/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree102.table
  base := (68706760419117440189893894572612682617131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-27514401252417037221868324790857686300000000000000)
      constant := (785713313339410425424678629273080992720073247061668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree102.table
  base := (17176689567624801579679033133713046695071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-13760646875559215305941398332343721900000000000000)
      constant := (393050901191983881808789986876423592641470323847976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250786972057868994679/50000000000000000000)
  centralHi := (501573944115737989359/100000000000000000000)
  directionLo := (504050867545528391431/100000000000000000000)
  directionHi := (63006358443191048929/12500000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree103.table
  base := (17750988571401886616309722708842185735023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-83319615355086071313246936075308883450000000000000)
      constant := (2402273011653975777759771222531108816058010845439728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree103.table
  base := (71003952346226975901131736107693904637073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-41670247785870146232674800434778927350000000000000)
      constant := (1201730487563213153955236443775172301565630072216066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504050867545528391431/100000000000000000000)
  centralHi := (63006358443191048929/12500000000000000000)
  directionLo := (15828614958204642719/3125000000000000000)
  directionHi := (506515678662548567009/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree104.table
  base := (7333246186593032346347194220792951117207/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-84096026952921030960888897778044708000000000000000)
      constant := (2447833622682361366003003810240296618758220374073880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree104.table
  base := (36666230057781704442368510628685510374669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-42058554945062646547525405872526689000000000000000)
      constant := (1224522148718077427550320982585693123491236388926196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15828614958204642719/3125000000000000000)
  centralHi := (506515678662548567009/100000000000000000000)
  directionLo := (101793710687559574539/20000000000000000000)
  directionHi := (63621069179724734087/12500000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree105.table
  base := (15138456469236375128841089575825720671409/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-28290812850251996869510286493593510850000000000000)
      constant := (831273924229495813140588399946380958413049194487260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree105.table
  base := (37846140383271130042570800043346041072957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-14148954034751715620792003770091483550000000000000)
      constant := (415842562277862679879236101359345700970513149396796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101793710687559574539/20000000000000000000)
  centralHi := (63621069179724734087/12500000000000000000)
  directionLo := (511409663622175661153/100000000000000000000)
  directionHi := (255704831811087830577/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree106.table
  base := (78083414998938373692110349441850904144317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96182280000000000000000000000000000000000000000
      center := (591441573)
      previous := (0)
      next := (524272875)
      square := (13817432690793337158423615301066800000000000000)
      linear := (-1616016040539451891625902286481440700000000000000)
      constant := (47929008703802603795050862189661230856816185810276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree106.table
  base := (78083413573493631393236655454120355913429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48091140000000000000000000000000000000000000000
      center := (295797999)
      previous := (0)
      next := (262059225)
      square := (6908716345396668579211807650533400000000000000)
      linear := (-808210740819766927872200316000419100000000000000)
      constant := (23976360409901585643387145377927313448808254191906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511409663622175661153/100000000000000000000)
  centralHi := (255704831811087830577/50000000000000000000)
  directionLo := (513839176886824396239/100000000000000000000)
  directionHi := (6422989711085304953/1250000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree107.table
  base := (80505859174056926216089840008707167504797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-86425261746425909903814782886252181650000000000000)
      constant := (2587080688190092255365918567167115054342589917904948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree107.table
  base := (80505857887862046310883488833694580879631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-43223476422640147492077222185769973950000000000000)
      constant := (1294180393226359633180147086623806730895390385117502) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513839176886824396239/100000000000000000000)
  centralHi := (6422989711085304953/1250000000000000000)
  directionLo := (516257256957528454531/100000000000000000000)
  directionHi := (129064314239382113633/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree108.table
  base := (41479807145228300013001872723145244112381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-29067224448086956517152248196329335400000000000000)
      constant := (878117151019311616769010143068429133461261678857336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree108.table
  base := (82959613130003086566675452075990313169129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-14537261193944215935642609207839245200000000000000)
      constant := (439275853730191096424085646919888494811026753336806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516257256957528454531/100000000000000000000)
  centralHi := (129064314239382113633/25000000000000000000)
  directionLo := (64833007967934183991/12500000000000000000)
  directionHi := (518664063743473471929/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree109.table
  base := (85444679828774901196697067422229695810771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-87978084942095829199098706291723830750000000000000)
      constant := (2682049755640312401256331229573642891517905437690764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree109.table
  base := (10680584847731755826007231464239944823297/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-44000090741025148121778433061265497250000000000000)
      constant := (1341688605485379609037862836295454958557667734635792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64833007967934183991/12500000000000000000)
  centralHi := (518664063743473471929/100000000000000000000)
  directionLo := (521059753460652786929/100000000000000000000)
  directionHi := (52105975346065278693/10000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree110.table
  base := (87961055324806250961597966160458221851/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-88754496539930788846740667994459655300000000000000)
      constant := (2730175595700588648155032091404860636242337501484000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree110.table
  base := (87961054380385270908010177164574007626453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-44388397900217648436629038499013258900000000000000)
      constant := (1365763525992760185340025672297410290135461540310026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521059753460652786929/100000000000000000000)
  centralHi := (52105975346065278693/10000000000000000000)
  directionLo := (523444478750190481947/100000000000000000000)
  directionHi := (130861119687547620487/25000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree111.table
  base := (90508740363639003038987657358160512274541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-29843636045921916164794209899065159950000000000000)
      constant := (926242991009085235290702689745217893128021399489148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree111.table
  base := (90508739511748839982313383183841768794679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-14925568353136716250493214645587006850000000000000)
      constant := (463350774202410733845078875839792202557974485644506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523444478750190481947/100000000000000000000)
  centralHi := (130861119687547620487/25000000000000000000)
  directionLo := (525818388791834633813/100000000000000000000)
  directionHi := (262909194395917316907/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree112.table
  base := (9308773457441648359639292957844708089969/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-90307319735600708142024591399931304400000000000000)
      constant := (2827709887431263420062714022036934854431466168113960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree112.table
  base := (93087733806050195010942646847961882629407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-45165012218602649066330249374508782200000000000000)
      constant := (1414554995234515807252199844579034383744630214816094) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525818388791834633813/100000000000000000000)
  centralHi := (262909194395917316907/50000000000000000000)
  directionLo := (52818162941285956571/10000000000000000000)
  directionHi := (528181629412859565711/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree113.table
  base := (4784901881282775429990357235924722181931/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-91083731333435667789666553102667128950000000000000)
      constant := (2877118338743632906089983063073022644557855528564080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree113.table
  base := (95698036932676254809266108152087082445927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-45553319377795149381180854812256543850000000000000)
      constant := (1439271543790343334633583391348230012269597674269934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52818162941285956571/10000000000000000000)
  centralHi := (528181629412859565711/100000000000000000000)
  directionLo := (530534343192602064131/100000000000000000000)
  directionHi := (132633585798150516033/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree114.table
  base := (9833964922106294986312990678128664787621/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-30620047643756875812436171601800984500000000000000)
      constant := (975651442271107992094125590081889650637697496153880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree114.table
  base := (98339648596120686613970816692331859043337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-15313875512329216565343820083334768500000000000000)
      constant := (488067322733131743551469932343342008681326981463718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530534343192602064131/100000000000000000000)
  centralHi := (132633585798150516033/25000000000000000000)
  directionLo := (532876669562843611637/100000000000000000000)
  directionHi := (266438334781421805819/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree115.table
  base := (50506284547898636706518023248023424515989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-92636554529105587084950476508138778050000000000000)
      constant := (2977217851505329398985760211557072728797508115834152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree115.table
  base := (2020251370645066727372282344683475098933/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-46329933696180150010882065687752067150000000000000)
      constant := (1489346268394349198164844317959690117689239699709300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532876669562843611637/100000000000000000000)
  centralHi := (266438334781421805819/50000000000000000000)
  directionLo := (133802186226059655291/25000000000000000000)
  directionHi := (107041748980847724233/20000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree116.table
  base := (25929199253281911099226770837321660621777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-93412966126940546732592438210874602600000000000000)
      constant := (3027908912698971823555263347049842682009161065645072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree116.table
  base := (20743359300997297486269994906115990409733/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-46718240855372650325732671125499828800000000000000)
      constant := (1514704444315030481768379212177819341052377867238930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133802186226059655291/25000000000000000000)
  centralHi := (107041748980847724233/20000000000000000000)
  directionLo := (268765351319488688887/50000000000000000000)
  directionHi := (21501228105559095111/4000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree117.table
  base := (106452332761448255265588720910013825243749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-31396459241591835460078133304536809050000000000000)
      constant := (1026342503428793928708298717840192246663767924402972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree117.table
  base := (21290466460659134480484615114016212954381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-15702182671521716880194425521082530150000000000000)
      constant := (513425498635884174425911671816129399415845727511670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268765351319488688887/50000000000000000000)
  centralHi := (21501228105559095111/4000000000000000000)
  directionLo := (269921336659930920849/50000000000000000000)
  directionHi := (539842673319861841699/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree118.table
  base := (54609588075805026964521666500567957292729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-94965789322610466027876361616346251700000000000000)
      constant := (3130573644171137515118408134860322577323737408006472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree118.table
  base := (109219175738557276597299662842587440826507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-47494855173757650955433882000995352100000000000000)
      constant := (1566062423124138361989081893305534693006355098394294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269921336659930920849/50000000000000000000)
  centralHi := (539842673319861841699/100000000000000000000)
  directionLo := (542144784715962589489/100000000000000000000)
  directionHi := (54214478471596258949/10000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree119.table
  base := (28004331753634021113848451311261994828577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-95742200920445425675518323319082076250000000000000)
      constant := (3182547314267049312815765723703588430930605294329872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree119.table
  base := (28004331660542300491635219819901147012081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-47883162332950151270284487438743113750000000000000)
      constant := (1592062225921514182263996603466637746805788664121608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542144784715962589489/100000000000000000000)
  centralHi := (54214478471596258949/10000000000000000000)
  directionLo := (272218580947507959793/50000000000000000000)
  directionHi := (544437161895015919587/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree120.table
  base := (28711696299772564190793273756486513633937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-32172870839426795107720095007272633600000000000000)
      constant := (1078316173499024375475022741587018265705312898656944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree120.table
  base := (114846784863424459040347648541576223132903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-16090489830714217195045030958830291800000000000000)
      constant := (539425301420455776058584930075160343075661695643642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272218580947507959793/50000000000000000000)
  centralHi := (544437161895015919587/100000000000000000000)
  directionLo := (34169995456419467493/6250000000000000000)
  directionHi := (546719927302711479889/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree121.table
  base := (23541510114034516019253074127260861567881/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-97295024116115344970802246724553725350000000000000)
      constant := (3287777262792339562710134271452773198963061487740020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree121.table
  base := (117707550267610768165202801908180000145729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-48659776651335151899985698314238637050000000000000)
      constant := (1644703458109361924091513291619401533517578850827618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34169995456419467493/6250000000000000000)
  centralHi := (546719927302711479889/100000000000000000000)
  directionLo := (21959728033560505879/4000000000000000000)
  directionHi := (8578018763109572609/1562500000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree122.table
  base := (12059962300701676929558686788653781468827/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-98071435713950304618444208427289549900000000000000)
      constant := (3341033541091286065406190416279839495905307078634680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree122.table
  base := (120599622734312121287846426171811059519821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-49048083810527652214836303751986398700000000000000)
      constant := (1671344887434805971573160722953388955537155035775482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21959728033560505879/4000000000000000000)
  centralHi := (8578018763109572609/1562500000000000000)
  directionLo := (17226784372863883169/3125000000000000000)
  directionHi := (551257099931644261409/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree123.table
  base := (12352300240166869993631334091533411928693/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-32949282437261754755362056710008458150000000000000)
      constant := (1131572451779627094417848417013759743417141559494040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree123.table
  base := (15440375269486352342195380906467313822477/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-16478796989906717509895636396578053450000000000000)
      constant := (566066730736754815431580908625758150762335895293424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17226784372863883169/3125000000000000000)
  centralHi := (551257099931644261409/100000000000000000000)
  directionLo := (553511739606875166231/100000000000000000000)
  directionHi := (69188967450859395779/12500000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree124.table
  base := (25295537731525296247855506481276462300821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-99624258909620223913728131832761199000000000000000)
      constant := (3448828705485931825291106974193936240017315755774820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree124.table
  base := (1264776884361307847835692938518360078959/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-49824698128912652844537514627481922000000000000000)
      constant := (1725269372411213502184694861672085858027643011327800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553511739606875166231/100000000000000000000)
  centralHi := (69188967450859395779/12500000000000000000)
  directionLo := (555757232557716273979/100000000000000000000)
  directionHi := (27787861627885813699/5000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree125.table
  base := (129463681688624963689207057328108748481931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-100400670507455183561370093535497023550000000000000)
      constant := (3503367591488462644064800683826925012925712410628204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree125.table
  base := (129463681489025010569342862137502986234737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-50213005288105153159388120065229683650000000000000)
      constant := (1752552428015731411192345783995611915837468892629954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555757232557716273979/100000000000000000000)
  centralHi := (27787861627885813699/5000000000000000000)
  directionLo := (111598737841929714307/20000000000000000000)
  directionHi := (34874605575603035721/6250000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree126.table
  base := (132480981417549327731038510969773991386983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-33725694035096714403004018412744282700000000000000)
      constant := (1186111337769054406663891695249714917499380684161524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree126.table
  base := (26496196247538359910566231842321034832417/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-16867104149099217824746241834325815100000000000000)
      constant := (593349786334740777542978749015414483176957341954190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111598737841929714307/20000000000000000000)
  centralHi := (34874605575603035721/6250000000000000000)
  directionLo := (560221217783989534373/100000000000000000000)
  directionHi := (280110608891994767187/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree127.table
  base := (16941198471933004271782834684440933544463/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-101953493703125102856654016940968672650000000000000)
      constant := (3613727970906892553210155767027847804226558647143136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree127.table
  base := (135529587613406122191084607354960836531921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-50989619606490153789089330940725206950000000000000)
      constant := (1807760165359169421903019392802299996702995754583682) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560221217783989534373/100000000000000000000)
  centralHi := (280110608891994767187/50000000000000000000)
  directionLo := (140609981089750209183/25000000000000000000)
  directionHi := (562439924359000836733/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree128.table
  base := (138609500700744876901532707610448913153067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5097660840000000000000000000000000000000000000000
      center := (31346403369)
      previous := (0)
      next := (27786462375)
      square := (732323932612046869396451610956540400000000000000)
      linear := (-102729905300960062504295978643704497200000000000000)
      constant := (3669549464256236713488193979858810467940095057179628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree128.table
  base := (69304750277366922082168054069510047879969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (15677293947)
      previous := (0)
      next := (13889138925)
      square := (366161966306023434698225805478270200000000000000)
      linear := (-51377926765682654103939936378472968600000000000000)
      constant := (1835684847064914159976536382484799344906424299171396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell146.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140609981089750209183/25000000000000000000)
  centralHi := (562439924359000836733/100000000000000000000)
  directionLo := (141162478232208747109/25000000000000000000)
  directionHi := (564649912928834988437/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 95749
  qDenominator := 180624
  table := BinomialMassData.Q95749_180624.Degree129.table
  base := (141720720138303182793604708497704697210577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10448801123)
      previous := (0)
      next := (9262154125)
      square := (244107977537348956465483870318846800000000000000)
      linear := (-34502105632931674050645980115480107250000000000000)
      constant := (1241932831109037787885678899976431256827959686890156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95749_180624.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 47887
  qDenominator := 90312
  table := BinomialMassData.Q47887_90312.Degree129.table
  base := (70860360003378947279405273589824496753081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5225764649)
      previous := (0)
      next := (4629712975)
      square := (122053988768674478232741935159423400000000000000)
      linear := (-17255411308291718139596847272073576750000000000000)
      constant := (621274468035819705585751498411871824767987938768268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47887_90312.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell146.Kernel129
