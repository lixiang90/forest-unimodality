import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell147.Parameters
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch000_049
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch050_099
import ForestUnimodality.BinomialMassData.Q47239_89464.Batch000_049
import ForestUnimodality.BinomialMassData.Q47239_89464.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree000.table
  base := (388873298015254674109186791/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1192302175782515988311516300000000000000)
      linear := (-65500191037127265814010713000000000000)
      constant := (388873298015254674109186791000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree000.table
  base := (388873298015254674109186791/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1192302175782515988311516300000000000000)
      linear := (-65500191037127265814010713000000000000)
      constant := (388873298015254674109186791000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree001.table
  base := (216595464320971530284220624194973398856209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-165615234693871371379131583771462369500000000000)
      constant := (27133192852954619078031656960038572279910057017201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree001.table
  base := (216549996620045649935042333995843022391933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-165656901928970670992560607792658932000000000000)
      constant := (27127529828348768445473005493270811631863198702237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49921412498889217363/100000000000000000000)
  directionHi := (12480353124722304341/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree002.table
  base := (63322179190926221227390980397761543208839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-323039048967237226867595818734619082000000000000)
      constant := (16012929586345722764345818910749801028160151246542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree002.table
  base := (25319398936381633321693090743975033687049/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-323122383437435826094453866777012207000000000000)
      constant := (16007096588558332811062424811315522097300669289805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49921412498889217363/100000000000000000000)
  centralHi := (12480353124722304341/25000000000000000000)
  directionLo := (70599538608750872963/100000000000000000000)
  directionHi := (17649884652187718241/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree003.table
  base := (78332856654589684247920310013708410045239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-480462863240603082356060053697775794500000000000)
      constant := (10183195256499841177945904339904419863369431222871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree003.table
  base := (15658970533549632202255094518025686023929/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-480587864945900981196347125761365482000000000000)
      constant := (10178643915786014723231266094069255700197512561405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70599538608750872963/100000000000000000000)
  centralHi := (17649884652187718241/25000000000000000000)
  directionLo := (86466422833680113569/100000000000000000000)
  directionHi := (8646642283368011357/10000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree004.table
  base := (51287973079552526209102861578999396468391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-637886677513968937844524288660932507000000000000)
      constant := (7096154637395431764550791261335998569145383112199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree004.table
  base := (6407473026149453846308706167271541531693/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-638053346454366136298240384745718757000000000000)
      constant := (7092985902918295922283019122902885381066431079016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86466422833680113569/100000000000000000000)
  centralHi := (8646642283368011357/10000000000000000000)
  directionLo := (49921412498889217363/50000000000000000000)
  directionHi := (99842824997778434727/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree005.table
  base := (35277594353856635932677423112092378438813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-795310491787334793332988523624089219500000000000)
      constant := (5472184867983677687403475784359126343586946546557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree005.table
  base := (2203557547518474800496893802106599776333/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-795518827962831291400133643730072032000000000000)
      constant := (5470155119615873707705096553457012845204008381392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49921412498889217363/50000000000000000000)
  centralHi := (99842824997778434727/100000000000000000000)
  directionLo := (111627671880323934613/100000000000000000000)
  directionHi := (55813835940161967307/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree006.table
  base := (7855179814251943295044627037996339611/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-952734306060700648821452758587245932000000000000)
      constant := (4665335544962422578250020196370550297303280092800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree006.table
  base := (12560520245125998080033963075389056878999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-952984309471296446502026902714425307000000000000)
      constant := (4664191563147747982051666224827290638459099543022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111627671880323934613/100000000000000000000)
  centralHi := (55813835940161967307/50000000000000000000)
  directionLo := (4891279514451083249/4000000000000000000)
  directionHi := (61140993930638540613/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree007.table
  base := (18235794976206748910196165313264601416181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-1110158120334066504309916993550402644500000000000)
      constant := (4346810107212798265721913632557360626630647191509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree007.table
  base := (18223619898929994151146816792747580309207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-1110449790979761601603920161698778582000000000000)
      constant := (4346373427762564889683243302710674012518389415223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4891279514451083249/4000000000000000000)
  centralHi := (61140993930638540613/50000000000000000000)
  directionLo := (66039821284566193197/50000000000000000000)
  directionHi := (26415928513826477279/20000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree008.table
  base := (1652341711707801956705763138008146147151/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-1267581934607432359798381228513559357000000000000)
      constant := (4346962935254407668847214056177084548500182926712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree008.table
  base := (13208746812885043113354423063291294560003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-1267915272488226756705813420683131857000000000000)
      constant := (4347131029920469929424547384517940736822455018467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66039821284566193197/50000000000000000000)
  centralHi := (26415928513826477279/20000000000000000000)
  directionLo := (70599538608750872963/50000000000000000000)
  directionHi := (141199077217501745927/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree009.table
  base := (9370364978968755971349451682336998872533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-1425005748880798215286845463476716069500000000000)
      constant := (4576373170495534540745328506482421142401928115637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree009.table
  base := (9361845636136534728714981965418555516363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-1425380753996691911807706679667485132000000000000)
      constant := (4577099910736257771120380035460325207306987918507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70599538608750872963/50000000000000000000)
  centralHi := (141199077217501745927/100000000000000000000)
  directionLo := (149764237496667652089/100000000000000000000)
  directionHi := (14976423749666765209/10000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree010.table
  base := (6301438715807986082472004050607876907967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-1582429563154164070775309698439872782000000000000)
      constant := (4986361392296286280172643813006205084547753048863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree010.table
  base := (6293960693628956948158589499684651405603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-1582846235505157066909599938651838407000000000000)
      constant := (4987637472243836031280716136088215485927842916867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149764237496667652089/100000000000000000000)
  centralHi := (14976423749666765209/10000000000000000000)
  directionLo := (157865367509287880971/100000000000000000000)
  directionHi := (39466341877321970243/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree011.table
  base := (758032331119787482540808502312788795191/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-1739853377427529926263773933403029494500000000000)
      constant := (5549190250325451970203127902669130457316935586995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree011.table
  base := (756695425983395531761022476323725873121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-1740311717013622222011493197636191682000000000000)
      constant := (5551028673866402608433475899593782572405455475845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157865367509287880971/100000000000000000000)
  centralHi := (39466341877321970243/25000000000000000000)
  directionLo := (2069632428292173603/1250000000000000000)
  directionHi := (165570594263373888241/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree012.table
  base := (1702487827167213294215647376050225754543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-1897277191700895781752238168366186207000000000000)
      constant := (6248096023925452833674668280234437330197787008527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree012.table
  base := (848225749092660992694987645201233375267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-1897777198522087377113386456620544957000000000000)
      constant := (6250522616590340549283532796553513492661272517126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2069632428292173603/1250000000000000000)
  centralHi := (165570594263373888241/100000000000000000000)
  directionLo := (86466422833680113569/50000000000000000000)
  directionHi := (172932845667360227139/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree013.table
  base := (-12070053843230333451356440825657245031/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-2054701005974261637240702403329342919500000000000)
      constant := (7072236374816213691492701735173406804873476403364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree013.table
  base := (-53757212173070336699164732482644122533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-2055242680030552532215279715604898232000000000000)
      constant := (7075284019902687317346262433482297960979669634363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86466422833680113569/50000000000000000000)
  centralHi := (172932845667360227139/100000000000000000000)
  directionLo := (44998553127083488661/25000000000000000000)
  directionHi := (35998842501666790929/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree014.table
  base := (-190273713391584113303309944009654511121/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-2212124820247627492729166638292499632000000000000)
      constant := (8014101826458864208714199718021128834493803382648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree014.table
  base := (-1527166355096857776302129772438380681899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-2212708161539017687317172974589251507000000000000)
      constant := (8017807144188742147163034237528887838434239510389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44998553127083488661/25000000000000000000)
  centralHi := (35998842501666790929/20000000000000000000)
  directionLo := (93394410917328902051/50000000000000000000)
  directionHi := (186788821834657804103/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree015.table
  base := (-690856952988876250094474634647643707121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-2369548634520993348217630873255656344500000000000)
      constant := (9068166354722781554443148046391586183217903315324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree015.table
  base := (-1383973912850372580631631649099546062753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-2370173643047482842419066233573604782000000000000)
      constant := (9072567874817298456577801642952877937582795773566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93394410917328902051/50000000000000000000)
  centralHi := (186788821834657804103/100000000000000000000)
  directionLo := (193344799227348726231/100000000000000000000)
  directionHi := (24168099903418590779/12500000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree016.table
  base := (-3806098832639836720070903281324814938949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-2526972448794359203706095108218813057000000000000)
      constant := (10230164892927294165474041831374704087715471862939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree016.table
  base := (-3810198324551961327070088551745500096323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-2527639124555947997520959492557958057000000000000)
      constant := (10235302095838832597278429927236535861904394841053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193344799227348726231/100000000000000000000)
  centralHi := (24168099903418590779/12500000000000000000)
  directionLo := (199685649995556869453/100000000000000000000)
  directionHi := (99842824997778434727/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree017.table
  base := (-4677440363528248907979493527837043441749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-2684396263067725059194559343181969769500000000000)
      constant := (11496691121442329590705893168754864246763443793739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree017.table
  base := (-146285988593111435251312192546867258149/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-2685104606064413152622852751542311332000000000000)
      constant := (11502603964226675650045220205954932947954259172448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199685649995556869453/100000000000000000000)
  centralHi := (99842824997778434727/50000000000000000000)
  directionLo := (102915628356474962727/50000000000000000000)
  directionHi := (41166251342589985091/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree018.table
  base := (-5399710392650689996165002603365363750379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-2841820077341090914683023578145126482000000000000)
      constant := (12864961467658694362528760496219118644140978703669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree018.table
  base := (-5403063651542915820063751629800377799139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-2842570087572878307724746010526664607000000000000)
      constant := (12871690169179996566312574811429982431432732020029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102915628356474962727/50000000000000000000)
  centralHi := (41166251342589985091/20000000000000000000)
  directionLo := (211798615826252618889/100000000000000000000)
  directionHi := (21179861582625261889/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree019.table
  base := (-5991367715909116552190197628072577876679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-2999243891614456770171487813108283194500000000000)
      constant := (14332667483993334498503050182293905663439194242969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree019.table
  base := (-599439173904935198758039684112384443757/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-3000035569081343462826639269511017882000000000000)
      constant := (14340252442087702699117042108076262225984503398270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211798615826252618889/100000000000000000000)
  centralHi := (21179861582625261889/10000000000000000000)
  directionLo := (217602392201466385667/100000000000000000000)
  directionHi := (54400598050366596417/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree020.table
  base := (-6467862823514319182465575169409805774069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-3156667705887822625659952048071439907000000000000)
      constant := (15897876940035689023105065402017534210805681409259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree020.table
  base := (-129411702399646706877000012562355089741/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-3157501050589808617928532528495371157000000000000)
      constant := (15906358711080565115695093932199102669522069882550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217602392201466385667/100000000000000000000)
  centralHi := (54400598050366596417/25000000000000000000)
  directionLo := (223255343760647869227/100000000000000000000)
  directionHi := (55813835940161967307/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree021.table
  base := (-6842203187469801594191809681576525397481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-3314091520161188481148416283034596619500000000000)
      constant := (17558963127983817956502684187692463669129879252791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree021.table
  base := (-684464995520946548759574420269348406539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-3314966532098273773030425787479724432000000000000)
      constant := (17568382432326630013573804188982466351465184014290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223255343760647869227/100000000000000000000)
  centralHi := (55813835940161967307/25000000000000000000)
  directionLo := (228768651575274412739/100000000000000000000)
  directionHi := (11438432578763720637/5000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree022.table
  base := (-890672447188305220636630342747240955111/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-3471515334434554336636880517997753332000000000000)
      constant := (19314551547791461031280372010684746919264071213768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree022.table
  base := (-3563787799544049067624384578585829954749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-3472432013606738928132319046464077707000000000000)
      constant := (19324949282785526563465065407204089367936393873478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228768651575274412739/100000000000000000000)
  centralHi := (11438432578763720637/5000000000000000000)
  directionLo := (234152179937436321573/100000000000000000000)
  directionHi := (117076089968718160787/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree023.table
  base := (-3663350363663410044321087823092138376223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-3628939148707920192125344752960910044500000000000)
      constant := (21163478053978536465448988899622928750738898739906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree023.table
  base := (-7328669272129204205596142050340857846679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-3629897495115204083234212305448430982000000000000)
      constant := (21174895306216142423371506543212883966935183912969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234152179937436321573/100000000000000000000)
  centralHi := (117076089968718160787/50000000000000000000)
  directionLo := (59853670937617628087/25000000000000000000)
  directionHi := (239414683750470512349/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree024.table
  base := (-931757928750647428174175884281448054941/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-3786362962981286047613808987924066757000000000000)
      constant := (23104755077638440707805728510774729848052276918808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree024.table
  base := (-1863956547300930285851502592354403208749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-3787362976623669238336105564432784257000000000000)
      constant := (23117233131081172955499457348780916254255558922956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59853670937617628087/25000000000000000000)
  centralHi := (239414683750470512349/100000000000000000000)
  directionLo := (244563975722554162451/100000000000000000000)
  directionHi := (61140993930638540613/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree025.table
  base := (-1878543625831535208101265643973384803789/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-3943786777254651903102273222887223469500000000000)
      constant := (25137543867566212936896236807697312229460504584716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree025.table
  base := (-939468945485762521664175412380748174199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-3944828458132134393437998823417137532000000000000)
      constant := (25151124206797361426240636862576513374488420605512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244563975722554162451/100000000000000000000)
  centralHi := (61140993930638540613/25000000000000000000)
  directionLo := (7800220702951440213/3125000000000000000)
  directionHi := (249607062494446086817/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree026.table
  base := (-375636765096459700093669557056132806127/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-4101210591528017758590737457850380182000000000000)
      constant := (27261131415264030792593683603982944660054926217940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree026.table
  base := (-7514145156617757985179101371065767141583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-4102293939640599548539892082401490807000000000000)
      constant := (27275855724236481849924984390146642757880639368913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7800220702951440213/3125000000000000000)
  centralHi := (249607062494446086817/100000000000000000000)
  directionLo := (254550256477950866183/100000000000000000000)
  directionHi := (31818782059743858273/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree027.table
  base := (-1863649047861720455450439649411540756311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-4258634405801383614079201692813536894500000000000)
      constant := (29474911136484425299553783738938499181611666259684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree027.table
  base := (-7455855778363066302617580782300274356159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-4259759421149064703641785341385844082000000000000)
      constant := (29490821293577072301591224305313917047521451457249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254550256477950866183/100000000000000000000)
  centralHi := (31818782059743858273/12500000000000000000)
  directionLo := (259399268501040340707/100000000000000000000)
  directionHi := (64849817125260085177/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree028.table
  base := (-7343886446547200341749468263635748640829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-4416058220074749469567665927776693607000000000000)
      constant := (31778366626247476227164632064397419988845480723619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree028.table
  base := (-7345011210938293913956470431589639051883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-4417224902657529858743678600370197357000000000000)
      constant := (31795504696534486714684454173407756640977067532213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259399268501040340707/100000000000000000000)
  centralHi := (64849817125260085177/25000000000000000000)
  directionLo := (264159285138264772789/100000000000000000000)
  directionHi := (26415928513826477279/10000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree029.table
  base := (-287364951406572438272486516249127650617/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-4573482034348115325056130162739850319500000000000)
      constant := (34171057960545891215712040389775035594936061132175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree029.table
  base := (-7185127756829519483143886997201403227399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-4574690384165995013845571859354550632000000000000)
      constant := (34189466186116646661877519800131645330611030260889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264159285138264772789/100000000000000000000)
  centralHi := (26415928513826477279/10000000000000000000)
  directionLo := (268835033711462771163/100000000000000000000)
  directionHi := (67208758427865692791/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree030.table
  base := (-6978306895657335891335964620342205601171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-4730905848621481180544594397703007032000000000000)
      constant := (36652610124945808191330739326749202042697116938381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree030.table
  base := (-6979202776252546546333164683182513487413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-4732155865674460168947465118338903907000000000000)
      constant := (36672330913986614823214692184281250242028522288043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268835033711462771163/100000000000000000000)
  centralHi := (67208758427865692791/25000000000000000000)
  directionLo := (136715418640809838621/50000000000000000000)
  directionHi := (273430837281619677243/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree031.table
  base := (-841124211379291090781159870249717742041/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-4888329662894847036033058632666163744500000000000)
      constant := (39222703228153533520305202330899303475273324783608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree031.table
  base := (-269191717868153696714764612981299968731/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-4889621347182925324049358377323257182000000000000)
      constant := (39243779143363145197058806787970377914932129038525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136715418640809838621/50000000000000000000)
  centralHi := (273430837281619677243/100000000000000000000)
  directionLo := (138975330726726307889/50000000000000000000)
  directionHi := (277950661453452615779/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree032.table
  base := (-6438367548645494064360851537982414279947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-5045753477168212891521522867629320457000000000000)
      constant := (41881064218113356440962719711909485953163525232917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree032.table
  base := (-3219540252221755642451447474861530011017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-5047086828691390479151251636307610457000000000000)
      constant := (41903537964894671882677979672519088146128099219374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138975330726726307889/50000000000000000000)
  centralHi := (277950661453452615779/100000000000000000000)
  directionLo := (70599538608750872963/25000000000000000000)
  directionHi := (282398154435003491853/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree033.table
  base := (-6108293417142271225409819248338368137589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-5203177291441578747009987102592477169500000000000)
      constant := (44627459865299916712862207395759434680978612967979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree033.table
  base := (-122178587012039389746009946416064972101/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-5204552310199855634253144895291963732000000000000)
      constant := (44651374280058278490251319329568338811224984180550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70599538608750872963/25000000000000000000)
  centralHi := (282398154435003491853/100000000000000000000)
  directionLo := (286776681503535665221/100000000000000000000)
  directionHi := (143388340751767832611/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree034.table
  base := (-5740365367142202829250279665613197044297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-5360601105714944602498451337555633882000000000000)
      constant := (47461690816056354541528990685470207183046406815767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree034.table
  base := (-5740932599088851655093366277992028803411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-5362017791708320789355038154276317007000000000000)
      constant := (47487088854842507320770389338528148644772138883021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286776681503535665221/100000000000000000000)
  centralHi := (143388340751767832611/50000000000000000000)
  directionLo := (72772338700937987093/25000000000000000000)
  directionHi := (291089354803751948373/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree035.table
  base := (-1067189382121183021982752147629357009983/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-5518024919988310457986915572518790594500000000000)
      constant := (50383586550273628622015092285933199161774165606565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree035.table
  base := (-1067290578380387363370192576568458453627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-5519483273216785944456931413260670282000000000000)
      constant := (50410511277935426189787376498035315470420885916985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72772338700937987093/25000000000000000000)
  centralHi := (291089354803751948373/100000000000000000000)
  directionLo := (18458691201778436397/6250000000000000000)
  directionHi := (295339059228454982353/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree036.table
  base := (-2448102602446470902940858898101177654123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-5675448734261676313475379807481947307000000000000)
      constant := (53393001103848773075707761757569365694054317753706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree036.table
  base := (-612082074783224093395967136283586489187/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-5676948754725251099558824672245023557000000000000)
      constant := (53421495683797825325165631714492139756099758036456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18458691201778436397/6250000000000000000)
  centralHi := (295339059228454982353/100000000000000000000)
  directionLo := (299528474993335304179/100000000000000000000)
  directionHi := (14976423749666765209/5000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree037.table
  base := (-1105535020658610635526184817070881315591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-5832872548535042168963844042445104019500000000000)
      constant := (56489809438223849554433246861260731347804542228004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree037.table
  base := (-2211271419546769921347156556283365975737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-5834414236233716254660717931229376832000000000000)
      constant := (56519917122878860676704550612377918228061188763214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299528474993335304179/100000000000000000000)
  centralHi := (14976423749666765209/5000000000000000000)
  directionLo := (75915024351951136527/25000000000000000000)
  directionHi := (303660097407804546109/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree038.table
  base := (-3914608701811555675612259911561879583917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-5990296362808408024452308277408260732000000000000)
      constant := (59673904357659744623623146928316578658668307361587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree038.table
  base := (-48937101642850629558498327517531205749/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-5991879717742181409762611190213730107000000000000)
      constant := (59705668479594830848320036833047844012898095819120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75915024351951136527/25000000000000000000)
  centralHi := (303660097407804546109/100000000000000000000)
  directionLo := (61547250851228634807/20000000000000000000)
  directionHi := (76934063564035793509/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree039.table
  base := (-1687173243486184900415783469357625594427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-6147720177081773879940772512371417444500000000000)
      constant := (62945193890338276267731657172263183520549651264394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree039.table
  base := (-1687333661996432336972253937090071708991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-6149345199250646564864504449198083382000000000000)
      constant := (62978657854139877580217051609212338507262957668802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61547250851228634807/20000000000000000000)
  centralHi := (76934063564035793509/25000000000000000000)
  directionLo := (31175912113278394083/10000000000000000000)
  directionHi := (311759121132783940831/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree040.table
  base := (-14009924642577061288433084464079985981/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-6305143991355139735429236747334574157000000000000)
      constant := (66303599062392896251275358288965710462117795258200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree040.table
  base := (-1401135695461274589397503425842417569459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-6306810680759111719966397708182436657000000000000)
      constant := (66338806337211159780136185089408825633477670907098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31175912113278394083/10000000000000000000)
  centralHi := (311759121132783940831/100000000000000000000)
  directionLo := (315730735018575761943/100000000000000000000)
  directionHi := (39466341877321970243/12500000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree041.table
  base := (-2198066719269482255265073808224334631509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-6462567805628505590917700982297730869500000000000)
      constant := (69749052004935750980682142858083392300227856161099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree041.table
  base := (-2198322563000900261404421499971792785179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-6464276162267576875068290967166789932000000000000)
      constant := (69786046117703935803042825884811264487184127486469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315730735018575761943/100000000000000000000)
  centralHi := (39466341877321970243/12500000000000000000)
  directionLo := (19978312896157543819/6250000000000000000)
  directionHi := (63930601267704140221/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree042.table
  base := (-62522345344262578333458670177571002367/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-6619991619901871446406165217260887582000000000000)
      constant := (73281494343402401757860097271414037162631629738425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree042.table
  base := (-156328720170897704848672880423937956357/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-6621741643776042030170184226151143207000000000000)
      constant := (73320318872689695111371337784492987202102892784270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19978312896157543819/6250000000000000000)
  centralHi := (63930601267704140221/20000000000000000000)
  directionLo := (323527729703558189591/100000000000000000000)
  directionHi := (40440966212944773699/12500000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree043.table
  base := (-897362491867035515160292659581709092121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-6777415434175237301894629452224044294500000000000)
      constant := (76900875826346411273110356103729776739052068813831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree043.table
  base := (-179513351780409769427159933984762965923/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-6779207125284507185272077485135496482000000000000)
      constant := (76941574396804559623619177217988172863540226033265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323527729703558189591/100000000000000000000)
  centralHi := (40440966212944773699/12500000000000000000)
  directionLo := (163678296753893780143/50000000000000000000)
  directionHi := (327356593507787560287/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree044.table
  base := (-100662250068840963674980877416064389221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-6934839248448603157383093687187201007000000000000)
      constant := (80607153157411477316889048595971806827185849263862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree044.table
  base := (-40301422435359196128015356912894174627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-6936672606792972340373970744119849757000000000000)
      constant := (80649769434773031950459536743187360905550353071985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163678296753893780143/50000000000000000000)
  centralHi := (327356593507787560287/100000000000000000000)
  directionLo := (2069632428292173603/625000000000000000)
  directionHi := (331141188526747776481/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree045.table
  base := (104951357824463903319116685756184621947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-7092263062721969012871557922150357719500000000000)
      constant := (84400288999779615546665835918169331223536125025415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree045.table
  base := (5245934785693367383021316573254418657/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-7094138088301437495475864003104203032000000000000)
      constant := (84444866686364748451210665226120216626736148627300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2069632428292173603/625000000000000000)
  centralHi := (331141188526747776481/100000000000000000000)
  directionLo := (334883015640971803841/100000000000000000000)
  directionHi := (167441507820485901921/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree046.table
  base := (640311843873705882370129739858572514353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-7249686876995334868360022157113514432000000000000)
      constant := (88280251127100520050125245018213743114141362691234) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree046.table
  base := (160059698191252070551670974235125246603/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-7251603569809902650577757262088556307000000000000)
      constant := (88326833957789794761784196623362880368029361326936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334883015640971803841/100000000000000000000)
  centralHi := (167441507820485901921/50000000000000000000)
  directionLo := (338583492791180855561/100000000000000000000)
  directionHi := (169291746395590427781/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree047.table
  base := (1033026788884355070872453601047114667799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-7407110691268700723848486392076671144500000000000)
      constant := (92247011698884759891869429745378350201043070389422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree047.table
  base := (2065922822288767336653725299310125158283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-7409069051318367805679650521072909582000000000000)
      constant := (92295643437516565832299798541203926547883416097387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338583492791180855561/100000000000000000000)
  centralHi := (169291746395590427781/50000000000000000000)
  directionLo := (171121980628264023549/50000000000000000000)
  directionHi := (342243961256528047099/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree048.table
  base := (288085396338434467527053165170317376593/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-7564534505542066579336950627039827857000000000000)
      constant := (96300546641705718567913231257166791151845411409770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree048.table
  base := (11522947595480987098367844102767851849/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-7566534532826832960781543780057262857000000000000)
      constant := (96351271077859005534566645011929622445465911290250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171121980628264023549/50000000000000000000)
  centralHi := (342243961256528047099/100000000000000000000)
  directionLo := (86466422833680113569/25000000000000000000)
  directionHi := (345865691334720454277/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree049.table
  base := (744971648511941834816413751918101945713/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-7721958319815432434825414862002984569500000000000)
      constant := (100440835120398081867664556162233484419763242603285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree049.table
  base := (3724753396125153090054371268820096285667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-7724000014335298115883437039041616132000000000000)
      constant := (100493696066523342372248946407054506137728813044163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86466422833680113569/25000000000000000000)
  centralHi := (345865691334720454277/100000000000000000000)
  directionLo := (174724943746112260771/50000000000000000000)
  directionHi := (349449887492224521543/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree050.table
  base := (574740261380814002200532283896005077037/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-7879382134088798290313879096966141282000000000000)
      constant := (104667859085845108131931280527097620231667722832744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree050.table
  base := (2298914076128932177033564868525549572879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-7881465495843763270985330298025969407000000000000)
      constant := (104722900374709082544472041716170885801056831997662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174724943746112260771/50000000000000000000)
  centralHi := (349449887492224521543/100000000000000000000)
  directionLo := (22062355815234647801/6250000000000000000)
  directionHi := (352997693043754364817/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree051.table
  base := (1099984073575021160751492575933343487279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-8036805948362164145802343331929297994500000000000)
      constant := (108981602887981080292099147372869325079512323702155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree051.table
  base := (5499836170572236312687666511757787330367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-8038930977352228426087223557010322682000000000000)
      constant := (109038868370393279562567586909908474196368871202463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22062355815234647801/6250000000000000000)
  centralHi := (352997693043754364817/100000000000000000000)
  directionLo := (14260407776503272559/4000000000000000000)
  directionHi := (44563774301572726747/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree052.table
  base := (6430744465139488564779171435847231303827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-8194229762635530001290807566892454707000000000000)
      constant := (113382052944356772382046782581867928255421408364403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree052.table
  base := (1607667242818979887202221252612963527537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-8196396458860693581189116815994675957000000000000)
      constant := (113441586487148535382322720631387637335617658594372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14260407776503272559/4000000000000000000)
  centralHi := (44563774301572726747/12500000000000000000)
  directionLo := (359988425016667909289/100000000000000000000)
  directionHi := (35998842501666790929/10000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree053.table
  base := (1478060007309342149119638371669081768169/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (53082485168013394315617017192300000000000000)
      linear := (-2973176780672444235236479815541335500000000000)
      constant := (41961266449296190489894697584114339556378260245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree053.table
  base := (7390232321835405970330444886488643214451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (53082485168013394315617017192300000000000000)
      linear := (-2973962954919600831716272721601648000000000000)
      constant := (41983283353614226524158778704211787697050572971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359988425016667909289/100000000000000000000)
  centralHi := (35998842501666790929/10000000000000000000)
  directionLo := (181716684410007730583/50000000000000000000)
  directionHi := (363433368820015461167/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree054.table
  base := (837850504906964986105469769508550718367/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-8509077391182261712267736036818768132000000000000)
      constant := (122443026164121307343166918189171804363008099344630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree054.table
  base := (8378444290240398400471696500010092109987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-8511327421877623891392903333963382507000000000000)
      constant := (122507227483479419827019122447089613779617906016643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181716684410007730583/50000000000000000000)
  centralHi := (363433368820015461167/100000000000000000000)
  directionLo := (366845963583831243677/100000000000000000000)
  directionHi := (183422981791915621839/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree055.table
  base := (939528811040057576679591322922997037497/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-8666501205455627567756200271781924844500000000000)
      constant := (127103530140216173890602266241172488458813261590330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree055.table
  base := (9395233573893485180043955912696939499993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-8668792903386089046494796592947735782000000000000)
      constant := (127170131199613311269473280864355029414795540083577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366845963583831243677/100000000000000000000)
  centralHi := (183422981791915621839/50000000000000000000)
  directionLo := (370227103847940732513/100000000000000000000)
  directionHi := (185113551923970366257/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree056.table
  base := (10440587031985875674666737509257031038233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-8823925019728993423244664506745081557000000000000)
      constant := (131850701607088862264029707492038506100798558442937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree056.table
  base := (10440538063922838648552186739136720953121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-8826258384894554201596689851932089057000000000000)
      constant := (131919746321400263500006909894531068690532905215169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370227103847940732513/100000000000000000000)
  centralHi := (185113551923970366257/50000000000000000000)
  directionLo := (74715528733863121641/20000000000000000000)
  directionHi := (186788821834657804103/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree057.table
  base := (2878586898356662847729955261608307725341/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-8981348834002359278733128741708238269500000000000)
      constant := (136684533783963992879176175419604439740252966242996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree057.table
  base := (11514303610718723180983496569961130836863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-8983723866403019356698583110916442332000000000000)
      constant := (136756066076917753431930801594490152491632729143007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74715528733863121641/20000000000000000000)
  centralHi := (186788821834657804103/50000000000000000000)
  directionLo := (376898399141469419819/100000000000000000000)
  directionHi := (18844919957073470991/5000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree058.table
  base := (6308261239560953043919795112571744024613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-9138772648275725134221592976671394982000000000000)
      constant := (141605020753576683344876939350159584812176310405514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree058.table
  base := (3154120740396327524550735494142640383659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-9141189347911484511800476369900795607000000000000)
      constant := (141679084556767786858200794977007705903964633961004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376898399141469419819/100000000000000000000)
  centralHi := (18844919957073470991/5000000000000000000)
  directionLo := (380190150715778865859/100000000000000000000)
  directionHi := (19009507535788943293/5000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree059.table
  base := (13747070362351118087352677306175281603877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-9296196462549090989710057211634551694500000000000)
      constant := (146612157347628383174258721409728938193171333038853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree059.table
  base := (549881393828724137075133864975186379023/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-9298654829419949666902369628885148882000000000000)
      constant := (146688796599644642893489410442422591583071917481175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380190150715778865859/100000000000000000000)
  centralHi := (19009507535788943293/5000000000000000000)
  directionLo := (11982926416982428163/3125000000000000000)
  directionHi := (383453645343437701217/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree060.table
  base := (7452977557829880639284633520999183698453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-9453620276822456845198521446597708407000000000000)
      constant := (151705939048038090461156483968151959035491324541034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree060.table
  base := (14905923185382814088088667885770794127677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-9456120310928414822004262887869502157000000000000)
      constant := (151785197693685307067808501728377731367231486377053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11982926416982428163/3125000000000000000)
  centralHi := (383453645343437701217/100000000000000000000)
  directionLo := (193344799227348726231/50000000000000000000)
  directionHi := (386689598454697452463/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree061.table
  base := (16093145129524983565447567455579016073009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-9611044091095822700686985681560865119500000000000)
      constant := (156886361901735029788616661598136509410197667232401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree061.table
  base := (16093116415284005128404127282198279025503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-9613585792436879977106156146853855432000000000000)
      constant := (156968283891350061901730423940963004243921323147967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193344799227348726231/50000000000000000000)
  centralHi := (386689598454697452463/100000000000000000000)
  directionLo := (15595947831610076631/4000000000000000000)
  directionHi := (761520890215335773/195312500000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree062.table
  base := (8654306361961939023290309091595985869243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-9768467905369188556175449916524021832000000000000)
      constant := (162153422447069680911254726455551854678830000793654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree062.table
  base := (17308586894755959391785583991160331847829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-9771051273945345132208049405838208707000000000000)
      constant := (162238051735911377187902388864917297614459920499381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15595947831610076631/4000000000000000000)
  centralHi := (761520890215335773/195312500000000000)
  directionLo := (393081595098045336557/100000000000000000000)
  directionHi := (196540797549022668279/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree063.table
  base := (9276166819837577542391775281489133666929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-9925891719642554411663914151487178544500000000000)
      constant := (167507117650201228188683343467013798630862048878562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree063.table
  base := (2319038799956947224673466026451358909163/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-9928516755453810287309942664822561982000000000000)
      constant := (167594498197910295492397512368475096883346677581656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393081595098045336557/100000000000000000000)
  centralHi := (196540797549022668279/50000000000000000000)
  directionLo := (396238927707397159183/100000000000000000000)
  directionHi := (24764932981712322449/6250000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree064.table
  base := (9679827440594270031077481526545121587/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-10083315533915920267152378386450335257000000000000)
      constant := (172947444850058619692605992173352661126599606360064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree064.table
  base := (19824265682748221200965244226150855377581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-10085982236962275442411835923806915257000000000000)
      constant := (173037620620178510180737077977374809458433181916109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396238927707397159183/100000000000000000000)
  centralHi := (24764932981712322449/6250000000000000000)
  directionLo := (199685649995556869453/50000000000000000000)
  directionHi := (399371299991113738907/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree065.table
  base := (660139153783478469211633966132848603099/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-10240739348189286122640842621413491969500000000000)
      constant := (178474401710675882905531742482604436425732967205152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree065.table
  base := (10562217046501720572876668933120137828623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-10243447718470740597513729182791268532000000000000)
      constant := (178567416670227684045477241939708642000226823907294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199685649995556869453/50000000000000000000)
  centralHi := (399371299991113738907/100000000000000000000)
  directionLo := (402479294725177654427/100000000000000000000)
  directionHi := (100619823681294413607/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree066.table
  base := (5613204049566931005713125659514188679369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-10398163162462651978129306856376648682000000000000)
      constant := (184087986179875555398701370193533501899028387929764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree066.table
  base := (701649976425056160752862367086399957659/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-10400913199979205752615622441775621807000000000000)
      constant := (184183884298980670501965282152005435758742597640032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402479294725177654427/100000000000000000000)
  centralHi := (100619823681294413607/25000000000000000000)
  directionLo := (25347717022165603043/6250000000000000000)
  directionHi := (405563472354649648689/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree067.table
  base := (23809362002904282707801433167432314547429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-10555586976736017833617771091339805394500000000000)
      constant := (189788196453421635391576637915719325005498112003781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree067.table
  base := (11904673367816531042587246858891502555751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-10558378681487670907717515700759975082000000000000)
      constant := (189887021704966757456849913385696357465191328142478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25347717022165603043/6250000000000000000)
  centralHi := (405563472354649648689/100000000000000000000)
  directionLo := (408624372173570824601/100000000000000000000)
  directionHi := (204312186086785412301/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree068.table
  base := (1574629852601416181571271903472378138267/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-10713010791009383689106235326302962107000000000000)
      constant := (195575030943889216670013527968006536432883077849008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree068.table
  base := (1259703194473553899961191243979339086021/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-10715844162996136062819408959744328357000000000000)
      constant := (195676827303228733817397395642567636216610266065380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408624372173570824601/100000000000000000000)
  centralHi := (204312186086785412301/50000000000000000000)
  directionLo := (102915628356474962727/25000000000000000000)
  directionHi := (411662513425899850909/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree069.table
  base := (5321390387671422155449882646293608404427/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-10870434605282749544594699561266118819500000000000)
      constant := (201448488253605228529393382024787027728353104789015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree069.table
  base := (13303469774333796459316585904832196119351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-10873309644504601217921302218728681632000000000000)
      constant := (201553299698296763159595625806639257183180138143278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102915628356474962727/25000000000000000000)
  centralHi := (411662513425899850909/100000000000000000000)
  directionLo := (25917399770865613429/6250000000000000000)
  directionHi := (82935679266769962973/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree070.table
  base := (1752998440380404316682245065561650465861/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-11027858419556115400083163796229275532000000000000)
      constant := (207408567151106235370226670203951971019427517680464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree070.table
  base := (28047963881938819696709780449233935095401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-11030775126013066373023195477713034907000000000000)
      constant := (207516437660675518848894440015317279791990015310089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25917399770865613429/6250000000000000000)
  centralHi := (82935679266769962973/20000000000000000000)
  directionLo := (52209062882423979133/12500000000000000000)
  directionHi := (83534500611878366613/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree071.table
  base := (29517138282904009999720473972386067423479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-11185282233829481255571628031192432244500000000000)
      constant := (213455266550637418771620351077852704952434205342231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree071.table
  base := (14758564110721523580706709768335490191587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-11188240607521531528125088736697388182000000000000)
      constant := (213566240106369145753232895859581127528911264638086) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52209062882423979133/12500000000000000000)
  centralHi := (83534500611878366613/20000000000000000000)
  directionLo := (84129059720831762717/20000000000000000000)
  directionHi := (210322649302079406793/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree072.table
  base := (3101443398913415257715351543685151964507/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-11342706048102847111060092266155588957000000000000)
      constant := (219588585494283664668122709740876807432185915569230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree072.table
  base := (31014424920081369366349711780403856976643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-11345706089029996683226981995681741457000000000000)
      constant := (219702706079035362362495851122873643196128058515427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84129059720831762717/20000000000000000000)
  centralHi := (210322649302079406793/50000000000000000000)
  directionLo := (423597231652505237779/100000000000000000000)
  directionHi := (21179861582625261889/5000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree073.table
  base := (6507971080536340204267937529498126334017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-11500129862376212966548556501118745669500000000000)
      constant := (225808523136380803306397696441502901564557421686565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree073.table
  base := (6507969445402003608483734413912133134757/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-11503171570538461838328875254666094732000000000000)
      constant := (225925834734417096698115247177321578734975892795865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423597231652505237779/100000000000000000000)
  centralHi := (21179861582625261889/5000000000000000000)
  directionLo := (26658045960128180369/6250000000000000000)
  directionHi := (85305747072410177181/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree074.table
  base := (34093396550190263106254143121810087665633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-11657553676649578822037020736081902382000000000000)
      constant := (232115078729903936659775071252267436825571765841537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree074.table
  base := (17046694589471685190932234069862157305487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-11660637052046926993430768513650448007000000000000)
      constant := (232235625326748896010706394403167219754123642232286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26658045960128180369/6250000000000000000)
  centralHi := (85305747072410177181/20000000000000000000)
  directionLo := (107360057026413078153/25000000000000000000)
  directionHi := (429440228105652312613/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree075.table
  base := (35675052151921261426421613317955591532349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-11814977490922944677525484971045059094500000000000)
      constant := (238508251614571656184339151287188339832587667909661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree075.table
  base := (1783752275258060213881480396345941763149/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-11818102533555392148532661772634801282000000000000)
      constant := (238632077196877182661594179549268176321525959417220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107360057026413078153/25000000000000000000)
  centralHi := (429440228105652312613/100000000000000000000)
  directionLo := (86466422833680113569/20000000000000000000)
  directionHi := (216166057084200283923/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree076.table
  base := (37284817538551894804522349123644151777323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-11972401305196310533013949206008215807000000000000)
      constant := (244988041206440838388805730332675296046110456167947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree076.table
  base := (37284811544420459781737710037040275237947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-11975568015063857303634555031619154557000000000000)
      constant := (245115189761869281468888309774408700538177005229083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86466422833680113569/20000000000000000000)
  centralHi := (216166057084200283923/50000000000000000000)
  directionLo := (217602392201466385667/50000000000000000000)
  directionHi := (87040956880586554267/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree077.table
  base := (38922688578336532109440678757596393316357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-12129825119469676388502413440971372519500000000000)
      constant := (251554446988797485965934990475869787051870996761573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree077.table
  base := (38922683172217666427476841661819261235077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-12133033496572322458736448290603507832000000000000)
      constant := (251684962505916896037295199251384289604728738495653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217602392201466385667/50000000000000000000)
  centralHi := (87040956880586554267/20000000000000000000)
  directionLo := (109514654211516211637/25000000000000000000)
  directionHi := (438058616846064846549/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree078.table
  base := (20294330806643653003220061028171034752631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-12287248933743042243990877675934529232000000000000)
      constant := (258207468504175505458644995557869587337843048531118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree078.table
  base := (317098880758275650414443412051196067801/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-12290498978080787613838341549587861107000000000000)
      constant := (258341394972366110047331790806997320284484308952192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109514654211516211637/25000000000000000000)
  centralHi := (438058616846064846549/100000000000000000000)
  directionLo := (440893977299499636451/100000000000000000000)
  directionHi := (110223494324874909113/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree079.table
  base := (42282733403211200145576550243947214695829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-12444672748016408099479341910897685944500000000000)
      constant := (264947105347358013980843087655406199662318040171381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree079.table
  base := (10570682251144637382456064450604858459277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-12447964459589252768940234808572214382000000000000)
      constant := (265084486756728669163690449334316300426400535717812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440893977299499636451/100000000000000000000)
  centralHi := (110223494324874909113/25000000000000000000)
  directionLo := (88742243975427160327/20000000000000000000)
  directionHi := (110927804969283950409/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree080.table
  base := (44004901076597012107219875606284540775979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-12602096562289773954967806145860842657000000000000)
      constant := (271773357159235287900154764429925687293043597214731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree080.table
  base := (44004897108493378817189454170134243091463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-12605429941097717924042128067556567657000000000000)
      constant := (271914237500548800326254172819688582312420143042407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88742243975427160327/20000000000000000000)
  centralHi := (110927804969283950409/25000000000000000000)
  directionLo := (223255343760647869227/50000000000000000000)
  directionHi := (89302137504259147691/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree081.table
  base := (9151032417495980988526866390513433984209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-12759520376563139810456270380823999369500000000000)
      constant := (278686223621410265695802811765584766781361433046005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree081.table
  base := (4575515850753402356558024436898897713607/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-12762895422606183079144021326540920932000000000000)
      constant := (278830646886016607495315472559692849614582097668230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223255343760647869227/50000000000000000000)
  centralHi := (89302137504259147691/20000000000000000000)
  directionLo := (449292712490002956269/100000000000000000000)
  directionHi := (44929271249000295627/10000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree082.table
  base := (23766757088763482771244275232924845760861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-12916944190836505665944734615787156082000000000000)
      constant := (285685704451456987262452847546465710535576685720058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree082.table
  base := (5941688868448102891541255239681507404493/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-12920360904114648234245914585525274207000000000000)
      constant := (285833714631233538004005053651574455409044887072616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449292712490002956269/100000000000000000000)
  centralHi := (44929271249000295627/10000000000000000000)
  directionLo := (452057616817268892519/100000000000000000000)
  directionHi := (11301440420431722313/2500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree083.table
  base := (3083747208917933645225733992424535486767/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-13074368005109871521433198850750312794500000000000)
      constant := (292771799398749826647065136117187329570208531513008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree083.table
  base := (24669976214191996432730067228488601883877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-13077826385623113389347807844509627482000000000000)
      constant := (292923440486047875197518415488895616432906689917706) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452057616817268892519/100000000000000000000)
  centralHi := (11301440420431722313/2500000000000000000)
  directionLo := (113701428187048557519/25000000000000000000)
  directionHi := (454805712748194230077/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree084.table
  base := (12793620950958343628965191042935137032883/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-13231791819383237376921663085713469507000000000000)
      constant := (299944508240792139300060896929560176290409296707148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree084.table
  base := (51174481174211390842397686370062620851463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-13235291867131578544449701103493980757000000000000)
      constant := (300099824228388965520011121684050559387184707682407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113701428187048557519/25000000000000000000)
  centralHi := (454805712748194230077/100000000000000000000)
  directionLo := (228768651575274412739/50000000000000000000)
  directionHi := (457537303150548825479/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree085.table
  base := (5303709798090477318407792453576585171161/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-13389215633656603232410127320676626219500000000000)
      constant := (307203830779982241325916287536837701786438096967290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree085.table
  base := (3314818475504278309982731697834724203947/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-13392757348640043699551594362478334032000000000000)
      constant := (307362865661038174390975850133294853786737197649328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228768651575274412739/50000000000000000000)
  centralHi := (457537303150548825479/100000000000000000000)
  directionLo := (14382896309511435963/3125000000000000000)
  directionHi := (460252681904365950817/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree086.table
  base := (54927796470109548547539952876476541838933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-13546639447929969087898591555639782932000000000000)
      constant := (314549766840762674344394389480487290690176581285237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree086.table
  base := (54927794328918673545879791667011156032663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-13550222830148508854653487621462687307000000000000)
      constant := (314712564608782592340781904851682375420244102089207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14382896309511435963/3125000000000000000)
  centralHi := (460252681904365950817/100000000000000000000)
  directionLo := (231476067135484722301/50000000000000000000)
  directionHi := (462952134270969444603/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree087.table
  base := (5684657802381925614396932627745978753437/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-13704063262203334943387055790602939644500000000000)
      constant := (321982316267105662629177895968396564646331257136930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree087.table
  base := (56846576091612543322388348640332595355997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-13707688311656974009755380880447040582000000000000)
      constant := (322148920915904458010462119581451071938327257905533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231476067135484722301/50000000000000000000)
  centralHi := (462952134270969444603/100000000000000000000)
  directionLo := (232817968621372722163/50000000000000000000)
  directionHi := (465635937242745444327/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree088.table
  base := (5879344153282165940026796631166999989311/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-13861487076476700798875520025566096357000000000000)
      constant := (329501478920293690681888050165597278526762391220790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree088.table
  base := (58793439789168949807663488583459449714851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-13865153793165439164857274139431393857000000000000)
      constant := (329671934443965279140417841071887810224560461771139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232817968621372722163/50000000000000000000)
  centralHi := (465635937242745444327/100000000000000000000)
  directionLo := (234152179937436321573/50000000000000000000)
  directionHi := (468304359874872643147/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree089.table
  base := (60768386010646954732157670419767309441657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-14018910890750066654363984260529253069500000000000)
      constant := (337107254676959348952344651626179896077787874733273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree089.table
  base := (60768384437126732740709391569779436363523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-14022619274673904319959167398415747132000000000000)
      constant := (337281605069848846088061825451834440697642704619747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234152179937436321573/50000000000000000000)
  centralHi := (468304359874872643147/100000000000000000000)
  directionLo := (470957663600135589777/100000000000000000000)
  directionHi := (235478831800067794889/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree090.table
  base := (62771410579716684879204959537438372605667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-14176334705023432509852448495492409782000000000000)
      constant := (344799643427353124018149549539869192416118813524163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree090.table
  base := (31385704579858127736340578567758085537697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-14180084756182369475061060657400100407000000000000)
      constant := (344977932684031855612373857029035225735925354113666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470957663600135589777/100000000000000000000)
  centralHi := (235478831800067794889/50000000000000000000)
  directionLo := (94719220505572728583/20000000000000000000)
  directionHi := (118399025631965910729/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree091.table
  base := (8100314307387039655106217987770011262231/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-14333758519296798365340912730455566494500000000000)
      constant := (352578645073811742289822857967169897394190205879672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree091.table
  base := (64802513177632262272559472957444963380701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-14337550237690834630162953916384453682000000000000)
      constant := (352760917189054790656618339155216282717076679521789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94719220505572728583/20000000000000000000)
  centralHi := (118399025631965910729/25000000000000000000)
  directionLo := (476219923727963091399/100000000000000000000)
  directionHi := (2381099618639815457/500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree092.table
  base := (33430848476829899312353414127466782027687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-14491182333570164220829376965418723207000000000000)
      constant := (360444259529403094764538065697826386193713840143886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree092.table
  base := (66861695797216592605547712293575224160291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-14495015719199299785264847175368806957000000000000)
      constant := (360630558498169116123633638971100533723046446551299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476219923727963091399/100000000000000000000)
  centralHi := (2381099618639815457/500000000000000000)
  directionLo := (59853670937617628087/12500000000000000000)
  directionHi := (478829367500941024697/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree093.table
  base := (68948957444498179703991053305363885335203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-14648606147843530076317841200381879919500000000000)
      constant := (368396486716726744501960526698198268869059455891267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree093.table
  base := (861861955011038447162003983464717648237/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-14652481200707764940366740434353160232000000000000)
      constant := (368586856534139821092375367813278136785736577671440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59853670937617628087/12500000000000000000)
  centralHi := (478829367500941024697/100000000000000000000)
  directionLo := (481424667634756216117/100000000000000000000)
  directionHi := (240712333817378108059/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree094.table
  base := (8883036922553139037764948729669615754147/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-14806029962116895931806305435345036632000000000000)
      constant := (376435326566851608455350710580346543208632287607064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree094.table
  base := (35532147219318806531507234550322486111291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-14809946682216230095468633693337513507000000000000)
      constant := (376629811228184924624932407557440373117075299180598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481424667634756216117/100000000000000000000)
  centralHi := (240712333817378108059/50000000000000000000)
  directionLo := (242003025824637026333/50000000000000000000)
  directionHi := (484006051649274052667/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree095.table
  base := (73207710270450073600346989534493270129277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-14963453776390261787294769670308193344500000000000)
      constant := (384560779018374662737153471956743886735290720559453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree095.table
  base := (18301927355141120637468952450880914610471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-14967412163724695250570526952321866782000000000000)
      constant := (384759422519035816884193818023659606203215049237276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242003025824637026333/50000000000000000000)
  centralHi := (484006051649274052667/100000000000000000000)
  directionLo := (60821717628631118871/12500000000000000000)
  directionHi := (486573741029048950969/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree096.table
  base := (75379201677105919017280505743299293703547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-15120877590663627642783233905271350057000000000000)
      constant := (392772844016586489791730715022600427966626505307483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree096.table
  base := (18844800227541407259953759995901733679961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-15124877645233160405672420211306220057000000000000)
      constant := (392975690352104274138138016849284596604920048799716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60821717628631118871/12500000000000000000)
  centralHi := (486573741029048950969/100000000000000000000)
  directionLo := (489127951445108324903/100000000000000000000)
  directionHi := (61140993930638540613/12500000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree097.table
  base := (38789384605265557987330283187904628617669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-15278301404936993498271698140234506769500000000000)
      constant := (401071521512731205574088445183236508468680298022282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree097.table
  base := (15515753703690686841813902036286829560141/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-15282343126741625560774313470290573332000000000000)
      constant := (401278614678743703611868210535629068810419141139745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell147.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489127951445108324903/100000000000000000000)
  centralHi := (61140993930638540613/12500000000000000000)
  directionLo := (491668892966366644469/100000000000000000000)
  directionHi := (49166889296636664447/10000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree098.table
  base := (9975801565402378485951629680055090464113/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-15435725219210359353760162375197663482000000000000)
      constant := (409456811463349807688813598112347298367388456946056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree098.table
  base := (19951602974677365816783194272885306017383/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (149108700836949624632568201293170700000000000000)
      linear := (-15439808608250090715876206729274926607000000000000)
      constant := (409668195455593675023603841231704214865570172389148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell147.Kernel098
