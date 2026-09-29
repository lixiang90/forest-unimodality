import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell035.Parameters
import ForestUnimodality.BinomialMassData.Q1733_3648.Batch000_049
import ForestUnimodality.BinomialMassData.Q1733_3648.Batch050_099
import ForestUnimodality.BinomialMassData.Q1733_3648.Batch100_149
import ForestUnimodality.BinomialMassData.Q1733_3648.Batch150_199
import ForestUnimodality.BinomialMassData.Q869_1824.Batch000_049
import ForestUnimodality.BinomialMassData.Q869_1824.Batch050_099
import ForestUnimodality.BinomialMassData.Q869_1824.Batch100_149
import ForestUnimodality.BinomialMassData.Q869_1824.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree000.table
  base := (48708176885044308882655173/625000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (356115741075037003926517800000000000000)
      linear := (21480821440224323777556936000000000000)
      constant := (389665415080354471061241384000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree000.table
  base := (48708176885044308882655173/625000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (356115741075037003926517800000000000000)
      linear := (21480821440224323777556936000000000000)
      constant := (389665415080354471061241384000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree001.table
  base := (112529748396007752545939120403262465599391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-343168239329541539482919950830750000000000)
      constant := (243815421116121082352814106571507123535155906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree001.table
  base := (449171891712818569401315260392381002748441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-688450915871716111176653601099000000000000)
      constant := (486606073057168194133742001107564110351561603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (6242216881624689001/12500000000000000000)
  directionHi := (49937735052997512009/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree002.table
  base := (270386861127562364034884602650588952174587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-1419200416557692043233868126699000000000000)
      constant := (293481065512069004600573774971892319580077721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree002.table
  base := (53871266561455202721674272079204623342639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-1423429290982958107655495525574000000000000)
      constant := (292368899489372599602572885040641972900390185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6242216881624689001/12500000000000000000)
  centralHi := (49937735052997512009/100000000000000000000)
  directionLo := (70622622186143391931/100000000000000000000)
  directionHi := (17655655546535847983/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree003.table
  base := (6824253734858177611706539466296926979479/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-717354784818767002500632117245500000000000)
      constant := (62089012687277436619825325428553004271047975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree003.table
  base := (33950504233502702202769034039654763695163/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-719469222031400034711445816683000000000000)
      constant := (61783736868379370868587234070710301594769215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70622622186143391931/100000000000000000000)
  centralHi := (17655655546535847983/25000000000000000000)
  directionLo := (17298938865340994401/20000000000000000000)
  directionHi := (43247347163352486003/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree004.table
  base := (455312860062437792554487635977369053697/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-1442464146177454985884962288387000000000000)
      constant := (62986374440763086512965240400024804394231375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree004.table
  base := (113185305917965816169185106287330766886119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-2893386041205442100613179374524000000000000)
      constant := (125292318006227572322527087678748970537666877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17298938865340994401/20000000000000000000)
  centralHi := (43247347163352486003/50000000000000000000)
  directionLo := (99875470105995024017/100000000000000000000)
  directionHi := (49937735052997512009/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree005.table
  base := (40196252324547077481759321453827774086339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-1808896115126759468018976400905750000000000)
      constant := (45653224466554951592064519970408555507380137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree005.table
  base := (39962186758829586192358489205462119609867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-1814182208158342048546010649499500000000000)
      constant := (45412146063883200128975946698644030224985961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99875470105995024017/100000000000000000000)
  centralHi := (49937735052997512009/50000000000000000000)
  directionLo := (1744752659701195311/1562500000000000000)
  directionHi := (22332834044175299981/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree006.table
  base := (29890705009046543194136704398037752911127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-725109361358687983384330171141500000000000)
      constant := (11812893062616890263587951816627855363416847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree006.table
  base := (59440563110030914379449313539296026410667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-1454447597142642031190287741158000000000000)
      constant := (23514683920699076637574118025506678034250787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1744752659701195311/1562500000000000000)
  centralHi := (22332834044175299981/20000000000000000000)
  directionLo := (3822561555941917887/3125000000000000000)
  directionHi := (24464393958028274477/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree007.table
  base := (23179760652550947810110150950904382036817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-2541760053025368432287004625943250000000000)
      constant := (29291164188471640320834659412104725042747811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree007.table
  base := (4610601098713166662344890834174968640321/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-2549160583269584045024852573974500000000000)
      constant := (29178310256755443793960405254650322374838215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3822561555941917887/3125000000000000000)
  centralHi := (24464393958028274477/20000000000000000000)
  directionLo := (16515353498508041209/12500000000000000000)
  directionHi := (132122827988064329673/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree008.table
  base := (4635275897212294186637383350668713492921/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-2908192021974672914421018738462000000000000)
      constant := (25562011601911223088747003547409741851333772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree008.table
  base := (36887157570399073385452389784321988099443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-5833299541650410086528547072424000000000000)
      constant := (50976653358424342026589029699847713111696769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16515353498508041209/12500000000000000000)
  centralHi := (132122827988064329673/100000000000000000000)
  directionLo := (141245244372286783863/100000000000000000000)
  directionHi := (17655655546535847983/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree009.table
  base := (30286200557129381235446133061360095115259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-2183082660615984931036688567320500000000000)
      constant := (15567041536683084626502242973098638867858499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree009.table
  base := (3013027116500216943506434265373000219089/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-1094712986126942013834564832816500000000000)
      constant := (7768859811889276314034796162029304457955645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141245244372286783863/100000000000000000000)
  centralHi := (17655655546535847983/12500000000000000000)
  directionLo := (74906602579496268013/50000000000000000000)
  directionHi := (149813205158992536027/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree010.table
  base := (25047973508561920318826685578359070378993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-7282111919746563757378093926999000000000000)
      constant := (44313451842199501361412579553564982595449419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree010.table
  base := (24918765624731755686710386938905448529813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-7303256291872894079486230921374000000000000)
      constant := (44273474255900272551102998774298038257787479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74906602579496268013/50000000000000000000)
  centralHi := (149813205158992536027/100000000000000000000)
  directionLo := (15791698395750143073/10000000000000000000)
  directionHi := (157916983957501430731/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree011.table
  base := (10421263332244081222557779793656458378999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-4007487928822586360823061076018250000000000)
      constant := (21696215292631116118171002776381583096330917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree011.table
  base := (2591535447023040971629994249471789906377/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-4019117333492068037982536422924500000000000)
      constant := (21697026238361095398715514632341098561925164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15791698395750143073/10000000000000000000)
  centralHi := (157916983957501430731/100000000000000000000)
  directionLo := (165624730050971375639/100000000000000000000)
  directionHi := (4140618251274284391/2500000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree012.table
  base := (2170196117942373215036607647421780856067/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-1457973299257296947652358396179000000000000)
      constant := (7267363599685781248845243635601457806160748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree012.table
  base := (1079092468858185235610630373306685742089/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-1462202173682563012073985795054000000000000)
      constant := (7274034056368215029865737515038333423153032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165624730050971375639/100000000000000000000)
  centralHi := (4140618251274284391/2500000000000000000)
  directionLo := (172989388653409944011/100000000000000000000)
  directionHi := (43247347163352486003/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree013.table
  base := (2883262124681887052557301809223231775877/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-9480703733442390650182178602111500000000000)
      constant := (44744245611500600994858384279075389910123955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree013.table
  base := (14331366329258795765820781760256103608649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-9508191417206620068922756694799000000000000)
      constant := (44821422841263334748693545048760219583166867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172989388653409944011/100000000000000000000)
  centralHi := (43247347163352486003/25000000000000000000)
  directionLo := (90026532157058973191/50000000000000000000)
  directionHi := (180053064314117946383/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree014.table
  base := (5942611879119472673299516580359144415643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-5106783835670499807225103413574500000000000)
      constant := (23340503930026490030223756455058320589641369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree014.table
  base := (5904745282083941293183740254418725866237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-5121584896158931032700799309637000000000000)
      constant := (23397628425616294106796694870411448863134671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90026532157058973191/50000000000000000000)
  centralHi := (180053064314117946383/100000000000000000000)
  directionLo := (186849895239808122107/100000000000000000000)
  directionHi := (46712473809952030527/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree015.table
  base := (9685743618294743624155224170084578218657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-3648810536413202859572745017395500000000000)
      constant := (16441683580490410745804965325776489768185177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree015.table
  base := (4808957995006820173544763666985591581283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-1829691361238184010313406757291500000000000)
      constant := (8246161574284594371195781654384962623343163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186849895239808122107/100000000000000000000)
  centralHi := (46712473809952030527/25000000000000000000)
  directionLo := (96704008103788860423/50000000000000000000)
  directionHi := (193408016207577720847/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree016.table
  base := (7758753039799146162120366461594510142911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-11679295547138217542986263277224000000000000)
      constant := (52612350367384125825959036472245854484772613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree016.table
  base := (1924472335754179132306488862685189048139/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-5856563271270173029179641234112000000000000)
      constant := (26401465420007615005809659288578119478269074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96704008103788860423/50000000000000000000)
  centralHi := (193408016207577720847/100000000000000000000)
  directionLo := (39950188042398009607/20000000000000000000)
  directionHi := (49937735052997512009/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree017.table
  base := (6059922457975542999821479683086354334941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-12412159485036826507254291502261500000000000)
      constant := (56494897819138592238671096673474642838491103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree017.table
  base := (1201058445615852224542546768226580232129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-12448104917651588054838124392699000000000000)
      constant := (56725360812264608006027930100853916331978535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39950188042398009607/20000000000000000000)
  centralHi := (49937735052997512009/25000000000000000000)
  directionLo := (51474639081904570941/25000000000000000000)
  directionHi := (41179711265523656753/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree018.table
  base := (7116800121477252386647544461863231631/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-2190837237155905911920386621216500000000000)
      constant := (10155888303110770663188866327598979580513120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree018.table
  base := (2252875086381085478962742041488471581387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-2197180548793805008552827719529000000000000)
      constant := (10201171968134025246282887111031994490880707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51474639081904570941/25000000000000000000)
  centralHi := (41179711265523656753/20000000000000000000)
  directionLo := (42373573311686035159/20000000000000000000)
  directionHi := (52966966639607543949/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree019.table
  base := (20097713730895801382410771425588537629/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (234)
      previous := (117)
      next := (117)
      square := (1068347223225111011779553400000000000000)
      linear := (-19221450638274299772562808798250000000000)
      constant := (91279428288804667452955223520014295905960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree019.table
  base := (634346766580332417298108588222466762133/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (468)
      previous := (234)
      next := (234)
      square := (2136694446450222023559106800000000000000)
      linear := (-38554187445634548608852654409000000000000)
      constant := (183429721744887762910079830995821376431995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42373573311686035159/20000000000000000000)
  centralHi := (52966966639607543949/25000000000000000000)
  directionLo := (108836770282662458339/50000000000000000000)
  directionHi := (217673540565324916679/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree020.table
  base := (50500877796937332400942296088865714291/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-7305375649366326700029188088687000000000000)
      constant := (35687873017798754153620848662586550121543060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree020.table
  base := (990381443409117788952687863255002450049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-7326520021492657022137325083062000000000000)
      constant := (35867153923593351731409087001267042653403067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108836770282662458339/50000000000000000000)
  centralHi := (217673540565324916679/100000000000000000000)
  directionLo := (223328340441752999809/100000000000000000000)
  directionHi := (22332834044175299981/10000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree021.table
  base := (189862309763478555328947846665055617489/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-5114538412210420788108801467470500000000000)
      constant := (25777045195485353357478778995738601170817645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree021.table
  base := (228558631515914038041898069368732353997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-2564669736349426006792248681766500000000000)
      constant := (12955903309850229304382133193367326322085834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223328340441752999809/100000000000000000000)
  centralHi := (22332834044175299981/10000000000000000000)
  directionLo := (1830747607320085483/800000000000000000)
  directionHi := (3575678920547041959/1562500000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree022.table
  base := (-12102010408353029908693880762191630699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-16076479174529871328594432627449000000000000)
      constant := (83753058420913020989190039452722155838952983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree022.table
  base := (-4338285286336840190880559849836966921/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-8061498396603899018616167007537000000000000)
      constant := (42102322429528300018124129210008851574122785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1830747607320085483/800000000000000000)
  centralHi := (3575678920547041959/1562500000000000000)
  directionLo := (58557184875616609361/25000000000000000000)
  directionHi := (46845747900493287489/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree023.table
  base := (-438640174394556574584771820450968905647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-8404671556214240146431230426243250000000000)
      constant := (45313677274495452201417736439847942472059299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree023.table
  base := (-226283370440837351997889664026386099269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-8428987584159520016855587969774500000000000)
      constant := (45563927972006211164576194272319964896483346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58557184875616609361/25000000000000000000)
  centralHi := (46845747900493287489/20000000000000000000)
  directionLo := (119746481985002024673/50000000000000000000)
  directionHi := (239492963970004049347/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree024.table
  base := (-828625245313190731937672355682638629763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-2923701175054514876188414846254000000000000)
      constant := (16323680283895198739727981204455192454655557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree024.table
  base := (-26281495773709212529404845394606496137/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-2932158923905047005031669644004000000000000)
      constant := (16415523646745101407022073856290005756625376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119746481985002024673/50000000000000000000)
  centralHi := (239492963970004049347/100000000000000000000)
  directionLo := (3822561555941917887/1562500000000000000)
  directionHi := (244643939580282744769/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree025.table
  base := (-2361337775228127582073379236877269771067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-18275070988225698221398517302561500000000000)
      constant := (105687140541583354010272075931090725431684439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree025.table
  base := (-2383327598612835621952909757515500167919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-18327931918541524026668859788499000000000000)
      constant := (106290432931737361965830409253388447693143723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3822561555941917887/1562500000000000000)
  centralHi := (244643939580282744769/100000000000000000000)
  directionLo := (249688675264987560043/100000000000000000000)
  directionHi := (62422168816246890011/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree026.table
  base := (-2997443273750578489142878344049556971111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-19007934926124307185666545527599000000000000)
      constant := (113853974203565195293382331682654189175286787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree026.table
  base := (-1508471998068920598483261106689063926833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-9531455146826383011573850856487000000000000)
      constant := (57255600286718106205998539614626962517239861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249688675264987560043/100000000000000000000)
  centralHi := (62422168816246890011/25000000000000000000)
  directionLo := (127316742749930367329/50000000000000000000)
  directionHi := (254633485499860734659/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree027.table
  base := (-3572270255275214966918563561891457159689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-6580266288007638716644857917545500000000000)
      constant := (40811774349633824200323883688501484746602271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree027.table
  base := (-3589543238713259184954286011175683755789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-6599296222921336006542181212483000000000000)
      constant := (41049404062888925378461432276107281289160171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127316742749930367329/50000000000000000000)
  centralHi := (254633485499860734659/100000000000000000000)
  directionLo := (16217755186257182251/6250000000000000000)
  directionHi := (259484082980114916017/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree028.table
  base := (-1022877845502351502891856740528436651401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-10236831400960762557101300988837000000000000)
      constant := (65712510962210802655095590832989374963065434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree028.table
  base := (-513349293067126649665045099972808750823/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-10266433521937625008052692780962000000000000)
      constant := (66097664115360350932420678575430667491434764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16217755186257182251/6250000000000000000)
  centralHi := (259484082980114916017/100000000000000000000)
  directionLo := (16515353498508041209/6250000000000000000)
  directionHi := (52849131195225731869/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree029.table
  base := (-1140001187808723606321822747629243467341/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-10603263369910067039235315101355750000000000)
      constant := (70408915585384732983130340887637541071614394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree029.table
  base := (-228675658478010110429292886929488781471/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-10633922709493246006292113743199500000000000)
      constant := (70823666563801474705480948405625816184169070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16515353498508041209/6250000000000000000)
  centralHi := (52849131195225731869/20000000000000000000)
  directionLo := (67230733338852327051/25000000000000000000)
  directionHi := (53784586671081861641/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree030.table
  base := (-155683272040062893627207754622744170333/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-3656565112953123840456443071291500000000000)
      constant := (25101549159200217432164047002499693734656592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree030.table
  base := (-1248448320964949762267186227235475141781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-3667137299016289001510511568479000000000000)
      constant := (25249965590486692866418592729566143197634118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67230733338852327051/25000000000000000000)
  centralHi := (53784586671081861641/20000000000000000000)
  directionLo := (68380059898107948309/25000000000000000000)
  directionHi := (273520239592431793237/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree031.table
  base := (-670073988572746511000261078645316651633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-11336127307808676003503343326393250000000000)
      constant := (80397811029069059533229185602080986312000844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree031.table
  base := (-5371116080204512918116020072662113706179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-22737802169208976005541911335349000000000000)
      constant := (161748939128303813164597537273242415231208143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68380059898107948309/25000000000000000000)
  centralHi := (273520239592431793237/100000000000000000000)
  directionLo := (17377596349282946467/6250000000000000000)
  directionHi := (278041541588527143473/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree032.table
  base := (-5699166220828693522861700256784642562889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-23405118553515960971274714877824000000000000)
      constant := (171373585291531393353295114230930232104391213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree032.table
  base := (-1427110911368567639625065009587844009843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-11736390272160109001010376629912000000000000)
      constant := (86195780971831478323398569407536729874680062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17377596349282946467/6250000000000000000)
  centralHi := (278041541588527143473/100000000000000000000)
  directionLo := (141245244372286783863/50000000000000000000)
  directionHi := (282490488744573567727/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree033.table
  base := (-3000062599970284278292718856888690137501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-4022997081902428322590457183810250000000000)
      constant := (30390072746692584881685978695605348875987139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree033.table
  base := (-6008297233870857783433302268396860200429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-8069252973143819999499865061433000000000000)
      constant := (61141643823565684536467313677041561592645131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141245244372286783863/50000000000000000000)
  centralHi := (282490488744573567727/100000000000000000000)
  directionLo := (286870447438162270483/100000000000000000000)
  directionHi := (71717611859540567621/25000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree034.table
  base := (-6265630547997721860966524846831702814837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-24870846429313178899810771327899000000000000)
      constant := (193693834500657691857368583606301250226531529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree034.table
  base := (-6272823661356201236214943054307494522113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-24942737294542701994978437108774000000000000)
      constant := (194846722707719337497718264537691920932551621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286870447438162270483/100000000000000000000)
  centralHi := (71717611859540567621/25000000000000000000)
  directionLo := (291184530831558423979/100000000000000000000)
  directionHi := (14559226541577921199/5000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree035.table
  base := (-3248762204956619095781409533884885161323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-12801855183605893932039399776468250000000000)
      constant := (102715892155048535132392044475967151792162191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree035.table
  base := (-812981442137184933269113475184106327879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-12838857834826971995728639516624500000000000)
      constant := (103327477635500876971422921360369131075128172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291184530831558423979/100000000000000000000)
  centralHi := (14559226541577921199/5000000000000000000)
  directionLo := (59087124952164722777/20000000000000000000)
  directionHi := (147717812380411806943/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree036.table
  base := (-6697377113676132976389966538029597570597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-8778858101703465609448942592658000000000000)
      constant := (72517528414420513601273814472564627777014483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree036.table
  base := (-6702938926005912476573652931496594548391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-8804231348255061995978706985908000000000000)
      constant := (72949313925415150560394041091888979368030849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59087124952164722777/20000000000000000000)
  centralHi := (147717812380411806943/50000000000000000000)
  directionLo := (74906602579496268013/25000000000000000000)
  directionHi := (299626410317985072053/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree037.table
  base := (-6866527680902909460495639579909768727739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-27069438243009005792614856003011500000000000)
      constant := (230054787139740430460094017878530622811608663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree037.table
  base := (-6871413775424714880666305964517858091691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-27147672419876427984414962882199000000000000)
      constant := (231424244056477729286643281098167269061698647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74906602579496268013/25000000000000000000)
  centralHi := (299626410317985072053/100000000000000000000)
  directionLo := (303759383628333246047/100000000000000000000)
  directionHi := (9492480738385413939/3125000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree038.table
  base := (-1751529555720465429322138780423588408601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (234)
      previous := (117)
      next := (117)
      square := (1068347223225111011779553400000000000000)
      linear := (-38507343740869272516458288404500000000000)
      constant := (336478051375358056443352038644200657048394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree038.table
  base := (-219075257017529125425533319438865103277/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (234)
      previous := (117)
      next := (117)
      square := (1068347223225111011779553400000000000000)
      linear := (-38618629909955221580185325217000000000000)
      constant := (338480105269996338865959366098403225042704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303759383628333246047/100000000000000000000)
  centralHi := (9492480738385413939/3125000000000000000)
  directionLo := (307836873237252564343/100000000000000000000)
  directionHi := (38479609154656570543/12500000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree039.table
  base := (-7117123160404693611702300041046175011153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-9511722039602074573716970817695500000000000)
      constant := (85399542601782794798038943632310600352223767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree039.table
  base := (-7120887737559111829163357689430049649031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-9539209723366303992457548910383000000000000)
      constant := (85907357341318596123674212258055330201699809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307836873237252564343/100000000000000000000)
  centralHi := (38479609154656570543/12500000000000000000)
  directionLo := (155930527725259495221/50000000000000000000)
  directionHi := (311861055450518990443/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree040.table
  base := (-7200374058276972765123326003945010291429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-29268030056704832685418940678124000000000000)
      constant := (269838310692075603652182467711731303854382393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree040.table
  base := (-7203675853030879352226124734115441603251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-29352607545210153973851488655624000000000000)
      constant := (271441660221216634514053821701587976743679167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155930527725259495221/50000000000000000000)
  centralHi := (311861055450518990443/100000000000000000000)
  directionLo := (315833967915002861461/100000000000000000000)
  directionHi := (157916983957501430731/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree041.table
  base := (-7256580742060688231258157409824192878367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-30000893994603441649686968903161500000000000)
      constant := (283855433012106540381132916420925082706478539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree041.table
  base := (-7259475218961101059450086338757008180027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-30087585920321395970330330580099000000000000)
      constant := (285540639628952284696109986447095394516030759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315833967915002861461/100000000000000000000)
  centralHi := (157916983957501430731/50000000000000000000)
  directionLo := (319757521680348331667/100000000000000000000)
  directionHi := (79939380420087082917/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree042.table
  base := (-7286349261102716516705161729441431723971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-10244585977500683537984999042733000000000000)
      constant := (99416446137999509108107381684560846272646469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree042.table
  base := (-3644442738985111500193704391552534349991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-5137094049238772994468195417429000000000000)
      constant := (50003060139034132640921022488286441349653249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319757521680348331667/100000000000000000000)
  centralHi := (79939380420087082917/25000000000000000000)
  directionLo := (4045418899303372239/1250000000000000000)
  directionHi := (323633511944269779121/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree043.table
  base := (-455637323429452821755876800011139110779/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-15733310935200329789111512676618250000000000)
      constant := (156509733190423758695205099758059754416085744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree043.table
  base := (-1823104620134050347774325083413177427371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-15778771335271939981644007214524500000000000)
      constant := (157437134751453270690155072298422862379814414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4045418899303372239/1250000000000000000)
  centralHi := (323633511944269779121/100000000000000000000)
  directionLo := (65492725530582459097/20000000000000000000)
  directionHi := (163731813826456147743/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree044.table
  base := (-1817141641581124618259401162181197444043/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-16099742904149634271245526789137000000000000)
      constant := (164082669068404876805466183780665245086202862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree044.table
  base := (-3635255615108995813289868192102425692699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-16146260522827560979883428176762000000000000)
      constant := (165053946180101586303838521048492947974806983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65492725530582459097/20000000000000000000)
  centralHi := (163731813826456147743/50000000000000000000)
  directionLo := (331249460101942751279/100000000000000000000)
  directionHi := (4140618251274284391/1250000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree045.table
  base := (-1805458781057575199612305225991025486037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-5488724957699646251126513633885250000000000)
      constant := (57281090774158280376916918505872536239706286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree045.table
  base := (-3611768451459241698359508952838287401177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-5504583236794393992707616379666500000000000)
      constant := (57619804209431976665580354913106354810675103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331249460101942751279/100000000000000000000)
  centralHi := (4140618251274284391/1250000000000000000)
  directionLo := (167496255331314749857/50000000000000000000)
  directionHi := (66998502132525899943/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree046.table
  base := (-1787581396046915109910578119642769786633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-16832606842048243235513555014174500000000000)
      constant := (179791368191306788668316589963703377829652922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree046.table
  base := (-7151814229911464933936482933934335281813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-33762477795877605952724540202474000000000000)
      constant := (361706723006103090882013097648959052389796521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167496255331314749857/50000000000000000000)
  centralHi := (66998502132525899943/20000000000000000000)
  directionLo := (16934709886965536343/5000000000000000000)
  directionHi := (338694197739310726861/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree047.table
  base := (-7054313774032322256516448107592020837033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-34398077621995095435295138253386500000000000)
      constant := (375853614628255327153056141297789962527243261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree047.table
  base := (-3527807745091639339064754728214580956747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-17248728085494423974601691063474500000000000)
      constant := (189035645365297328205430543123769601011342999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16934709886965536343/5000000000000000000)
  centralHi := (338694197739310726861/100000000000000000000)
  directionLo := (342355863049690872247/100000000000000000000)
  directionHi := (42794482881211359031/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree048.table
  base := (-1386807094410439000973235570551088480767/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-11710313853297901466521055492808000000000000)
      constant := (130832974677996375509414965809844285292215565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree048.table
  base := (-277406932812451826655963466374310521507/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-11744144848700029981894074683808000000000000)
      constant := (131604092161551087915615241328575847543399325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342355863049690872247/100000000000000000000)
  centralHi := (42794482881211359031/12500000000000000000)
  directionLo := (172989388653409944011/50000000000000000000)
  directionHi := (345978777306819888023/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree049.table
  base := (-339484612746050260906204906959175408819/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-17931902748896156681915597351730750000000000)
      constant := (204759223146138664813245973197114065869365230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree049.table
  base := (-3395343259268063721250462986822942386601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-17983706460605665971080532987949500000000000)
      constant := (205964732484892165294039787691915745582811117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172989388653409944011/50000000000000000000)
  centralHi := (345978777306819888023/100000000000000000000)
  directionLo := (349564145370982584061/100000000000000000000)
  directionHi := (174782072685491292031/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree050.table
  base := (-6621456485578807784707007557304698899353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-36596669435690922328099222928499000000000000)
      constant := (426911994734055857003641895318441745467000701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree050.table
  base := (-6622324992976068818457654169218410591933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-36702391296322573938639907900374000000000000)
      constant := (429422672175495743653142135650022398828936561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349564145370982584061/100000000000000000000)
  centralHi := (174782072685491292031/50000000000000000000)
  directionLo := (176556555465358479829/50000000000000000000)
  directionHi := (353113110930716959659/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree051.table
  base := (-321473778434508184260308813732181623913/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-6221588895598255215394541858922750000000000)
      constant := (74113234953345498186285733101790755978299070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree051.table
  base := (-803779247665001513368231741257625371523/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-6239561611905635989186458304141500000000000)
      constant := (74548623468228405427900777622923965526020788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176556555465358479829/50000000000000000000)
  centralHi := (353113110930716959659/100000000000000000000)
  directionLo := (178313380382258609123/50000000000000000000)
  directionHi := (356626760764517218247/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree052.table
  base := (-310693779107981947799045385446137628031/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-19031198655744070128317639689287000000000000)
      constant := (231410277353979040475666165334871548238424270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree052.table
  base := (-9943260240288103624413152457172921729/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-38172348046545057931597591749324000000000000)
      constant := (465536536398967484954619176929382828604683125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178313380382258609123/50000000000000000000)
  centralHi := (356626760764517218247/100000000000000000000)
  directionLo := (90026532157058973191/25000000000000000000)
  directionHi := (72021225725647178553/20000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree053.table
  base := (-5974764376945420560637095691448503554183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-38795261249386749220903307603611500000000000)
      constant := (481335312895123416022910508476132547994569811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree053.table
  base := (-5975342166050082025825634550730387972897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-38907326421656299928076433673799000000000000)
      constant := (484156943965974055598063024761940599200352549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90026532157058973191/25000000000000000000)
  centralHi := (72021225725647178553/20000000000000000000)
  directionLo := (181776099403798786683/50000000000000000000)
  directionHi := (363552198807597573367/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree054.table
  base := (-5712234223635368699528556666755480730791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-13176041729095119395057111942883000000000000)
      constant := (166741194784174113911821916273493974581184449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree054.table
  base := (-5712738316049129834294062387864925409791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-13214101598922513974851758532758000000000000)
      constant := (167717621729313398692867209474130574427065449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181776099403798786683/50000000000000000000)
  centralHi := (363552198807597573367/100000000000000000000)
  directionLo := (11467684667825753661/3125000000000000000)
  directionHi := (366965909370424117153/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree055.table
  base := (-678295509069576225025963124021280227487/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-20130494562591983574719682026843250000000000)
      constant := (259742641788475290083979393476903280851401316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree055.table
  base := (-542680374494866391647099284061524071167/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-20188641585939391960517058761374500000000000)
      constant := (261262107987789209922592738638324464342130695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11467684667825753661/3125000000000000000)
  centralHi := (366965909370424117153/100000000000000000000)
  directionLo := (370348155149024204361/100000000000000000000)
  directionHi := (185174077574512102181/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree056.table
  base := (-5117221484260112377185790816360668447743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-40993853063082576113707392278724000000000000)
      constant := (539120337400331432419173938965099146071094331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree056.table
  base := (-5117604865067911447419601645272730359137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-41112261546990025917512959447224000000000000)
      constant := (542270924404347003867221152002308633021054629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370348155149024204361/100000000000000000000)
  centralHi := (185174077574512102181/50000000000000000000)
  directionLo := (186849895239808122107/50000000000000000000)
  directionHi := (74739958095923248843/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree057.table
  base := (-2392432139392891381945070113453998196443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (356115741075037003926517800000000000000)
      linear := (-19264412281154748420117922670250000000000)
      constant := (258138819576898282516163162835415142428557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree057.table
  base := (-4785198487202769109450203842644645129453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (156)
      previous := (78)
      next := (78)
      square := (712231482150074007853035600000000000000)
      linear := (-38640110731395445903962882153000000000000)
      constant := (519291716480289928012711524847808479870547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186849895239808122107/50000000000000000000)
  centralHi := (74739958095923248843/20000000000000000000)
  directionLo := (377021631722547792779/100000000000000000000)
  directionHi := (18851081586127389639/5000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree058.table
  base := (-4429341944943638536855817322043220542761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-42459580938879794042243448728799000000000000)
      constant := (579510267390260073665077727744652551527189837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree058.table
  base := (-4429633213600900683324655925020342285813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-42582218297212509910470643296174000000000000)
      constant := (582890176970765164482256674919103406804464521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377021631722547792779/100000000000000000000)
  centralHi := (18851081586127389639/5000000000000000000)
  directionLo := (380314459584375824667/100000000000000000000)
  directionHi := (95078614896093956167/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree059.table
  base := (-810139368950009358427261192680308778159/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-43192444876778403006511476953836500000000000)
      constant := (600265044082362888059352967072378280310019015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree059.table
  base := (-4050950627916556037807895636905238574667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-43317196672323751906949485220649000000000000)
      constant := (603762623437082968592819004951789735998635639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380314459584375824667/100000000000000000000)
  centralHi := (95078614896093956167/25000000000000000000)
  directionLo := (191789510630260491957/50000000000000000000)
  directionHi := (76715804252104196783/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree060.table
  base := (-182448262148603665318574299198108067767/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-7320884802446168661796584196479000000000000)
      constant := (103565495667521231812789023137594986125361130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree060.table
  base := (-3649186311909762067958230800763018480511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-14684058349144997967809442381708000000000000)
      constant := (208336743270687098414035141378835800328535529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191789510630260491957/50000000000000000000)
  centralHi := (76715804252104196783/20000000000000000000)
  directionLo := (386816032415155441693/100000000000000000000)
  directionHi := (193408016207577720847/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree061.table
  base := (-1612089093659980004066421585941948643579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-22329086376287810467523766701955750000000000)
      constant := (321447011766941695054289161947825727040878943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree061.table
  base := (-322437071425795733377967041199786766679/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-22393576711273117949953584534799500000000000)
      constant := (323316481559891239234815795365616834345933215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386816032415155441693/100000000000000000000)
  centralHi := (193408016207577720847/50000000000000000000)
  directionLo := (19501308950659309643/5000000000000000000)
  directionHi := (390026179013186192861/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree062.table
  base := (-694090565267762691615264602974769541927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-22695518345237114949657780814474500000000000)
      constant := (332384081939470761172357232442228891359686118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree062.table
  base := (-555305978621417288165351964375104981279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-45522131797657477896386010994074000000000000)
      constant := (668630795139274460267581932120547744026374215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19501308950659309643/5000000000000000000)
  centralHi := (390026179013186192861/100000000000000000000)
  directionLo := (393210119017618032431/100000000000000000000)
  directionHi := (24575632438601127027/6250000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree063.table
  base := (-92221609068374979646561744079389172039/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-15374633542790946287861196617995500000000000)
      constant := (229005123462843861425273531068826594753598025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree063.table
  base := (-2305686150804775189734601290762474797611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-15419036724256239964288284306183000000000000)
      constant := (230334567239031587297956210852157574723062429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393210119017618032431/100000000000000000000)
  centralHi := (24575632438601127027/6250000000000000000)
  directionLo := (49546060495524123627/12500000000000000000)
  directionHi := (396368483964192989017/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree064.table
  base := (-1811731576439887403940768176765603523713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-46856764566271447827851618079024000000000000)
      constant := (709635621952595608313796724964018851383818821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree064.table
  base := (-905929288273363153245246114308372886509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-23496044273939980944671847421512000000000000)
      constant := (356875831089822218648123724472012032163910753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49546060495524123627/12500000000000000000)
  centralHi := (396368483964192989017/100000000000000000000)
  directionLo := (39950188042398009607/10000000000000000000)
  directionHi := (399501880423980096071/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree065.table
  base := (-1294953003114118094019651398311738588033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-47589628504170056792119646304061500000000000)
      constant := (732628900492775388996508482096253133202910261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree065.table
  base := (-323765877589482124222600799884751644293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-23863533461495601942911268383749500000000000)
      constant := (368437329415338211853170672581140370125961362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39950188042398009607/10000000000000000000)
  centralHi := (399501880423980096071/100000000000000000000)
  directionLo := (402610891363509275257/100000000000000000000)
  directionHi := (201305445681754637629/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree066.table
  base := (-377609401562227986354884496227158582371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-8053748740344777626064612421516500000000000)
      constant := (125999198421012994765251355932017909814264069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree066.table
  base := (-75531493986246943920512143074358290757/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-8077007549683740980383563115329000000000000)
      constant := (126728779420265639028097176440694939535183615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402610891363509275257/100000000000000000000)
  centralHi := (201305445681754637629/50000000000000000000)
  directionLo := (20284803870554359143/5000000000000000000)
  directionHi := (405696077411087182861/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree067.table
  base := (-192541221136486662979398341617587312981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-49055356379967274720655702754136500000000000)
      constant := (779734478791530517869121041046416367783791577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree067.table
  base := (-24078104952327762452604984874461533469/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-24598511836606843939390110308224500000000000)
      constant := (392122851141975029530296471208757012324512292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20284803870554359143/5000000000000000000)
  centralHi := (405696077411087182861/100000000000000000000)
  directionLo := (408757978037085192223/100000000000000000000)
  directionHi := (12773686813658912257/3125000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree068.table
  base := (98267313727693931224498490099546788251/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-24894110158932941842461865489587000000000000)
      constant := (401923376965347542273960517069047087093351666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree068.table
  base := (196498269316954627219919997724912073341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-24966001024162464937629531270462000000000000)
      constant := (404246862507555499330376159550428954775428303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408757978037085192223/100000000000000000000)
  centralHi := (12773686813658912257/3125000000000000000)
  directionLo := (51474639081904570941/12500000000000000000)
  directionHi := (411797112655236567529/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree069.table
  base := (500801820667517190196923944214058825709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-8420180709294082108198626534035250000000000)
      constant := (138055334369040623530350947393314550626705949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree069.table
  base := (1001540417686947265968886666302293564299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-16888993474478723957245968155133000000000000)
      constant := (277705578403120065630473830183742831101711939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51474639081904570941/12500000000000000000)
  centralHi := (411797112655236567529/100000000000000000000)
  directionLo := (3318511853210476373/800000000000000000)
  directionHi := (207406990825654773313/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree070.table
  base := (1633054242617527826697201071650613157363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-51253948193663101613459787429249000000000000)
      constant := (853190227307929669092288719464195973424424129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree070.table
  base := (816499641224676672834049591506861656733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-25700979399273706934108373194937000000000000)
      constant := (429057362363926975330195252569591149924241839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3318511853210476373/800000000000000000)
  centralHi := (207406990825654773313/50000000000000000000)
  directionLo := (104452266836231332471/25000000000000000000)
  directionHi := (83561813468985065977/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree071.table
  base := (285926808303420080794568672161379654427/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-25993406065780855288863907827143250000000000)
      constant := (439210705036129254270685080237612625959852764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree071.table
  base := (1143683349102368941525878450423255948691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-26068468586829327932347794157174500000000000)
      constant := (441743843300897205009751663703234253379932353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104452266836231332471/25000000000000000000)
  centralHi := (83561813468985065977/20000000000000000000)
  directionLo := (420782834889756079353/100000000000000000000)
  directionHi := (210391417444878039677/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree072.table
  base := (2964678665267914433461596444681827885589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-17573225356486773180665281293108000000000000)
      constant := (301341849463663807265249718811457389866697629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree072.table
  base := (1482318577549106703968486694885503897307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-8811985924794982976862405039804000000000000)
      constant := (151539269144001455306425315224894166906927827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420782834889756079353/100000000000000000000)
  centralHi := (210391417444878039677/50000000000000000000)
  directionLo := (42373573311686035159/10000000000000000000)
  directionHi := (423735733116860351591/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree073.table
  base := (458105250112761403757320183179994259409/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-26726270003679464253131936052180750000000000)
      constant := (465001318512158815883480881363078951928634788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree073.table
  base := (916201483763839558613434682080233623807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-26803446961940569928826636081649500000000000)
      constant := (467679252202411158715869488111461903216665962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42373573311686035159/10000000000000000000)
  centralHi := (423735733116860351591/100000000000000000000)
  directionLo := (42666819532548530341/10000000000000000000)
  directionHi := (426668195325485303411/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree074.table
  base := (2193950164135096674513943734597449958567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-27092701972628768735265950164699500000000000)
      constant := (478176335741568742929928749575835592992628061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree074.table
  base := (4387868997888356760315032525753960333679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-54341872298992381854132114087774000000000000)
      constant := (961856350848711762501787738943970976541374357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42666819532548530341/10000000000000000000)
  centralHi := (426668195325485303411/100000000000000000000)
  directionLo := (429580640025280766073/100000000000000000000)
  directionHi := (214790320012640383037/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree075.table
  base := (5133850096090135343685037403322279486051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-18306089294385382144933309518145500000000000)
      constant := (327691882640470828511892337360973268675714411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree075.table
  base := (2566911441907738037331071398327897392529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-9179475112350603975101826002041500000000000)
      constant := (164788191741455575051039699072050472521202969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429580640025280766073/100000000000000000000)
  centralHi := (214790320012640383037/50000000000000000000)
  directionLo := (108118367908381215007/25000000000000000000)
  directionHi := (432473471633524860029/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree076.table
  base := (5902688261736318927431231394285418154713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (468)
      previous := (234)
      next := (234)
      square := (2136694446450222023559106800000000000000)
      linear := (-154158259892118436008498495234000000000000)
      constant := (2798259177407144343074885936057793754464139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree076.table
  base := (5902664630022478623781781337255448181353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (468)
      previous := (234)
      next := (234)
      square := (2136694446450222023559106800000000000000)
      linear := (-154603404568462232263406642484000000000000)
      constant := (2814340443202658065303099311809516344544059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108118367908381215007/25000000000000000000)
  centralHi := (432473471633524860029/100000000000000000000)
  directionLo := (108836770282662458339/25000000000000000000)
  directionHi := (435347081130649833357/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree077.table
  base := (6694412218341022571537240699154430796441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-56383995758953364363335985004511500000000000)
      constant := (1037640414027599610387314176924909338396295603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree077.table
  base := (1673597924809588035999450938653801400353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-28273403712163053921784319930599500000000000)
      constant := (521799798371562795012384222979608563520664598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108836770282662458339/25000000000000000000)
  centralHi := (435347081130649833357/100000000000000000000)
  directionLo := (438201846677076413037/100000000000000000000)
  directionHi := (219100923338538206519/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree078.table
  base := (150180394647184194955222065691645048477/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-9519476616141995554600668871591500000000000)
      constant := (177580366408890786431238671537490385625004925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree078.table
  base := (1501800383718292352924169710741071588099/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-19093928599812449946682493928558000000000000)
      constant := (357199079445470518364110133040376946716518695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438201846677076413037/100000000000000000000)
  centralHi := (219100923338538206519/50000000000000000000)
  directionLo := (17641525367764471677/4000000000000000000)
  directionHi := (220519067097055895963/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree079.table
  base := (2086627222522903680647738164370670153117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-28924861817375291145936020727293250000000000)
      constant := (546848457124339063830497014202475057098526422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree079.table
  base := (4173246713631612673805218214757827648839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-29008382087274295918263161855074500000000000)
      constant := (549984911380375466160803435980825219531192637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17641525367764471677/4000000000000000000)
  centralHi := (220519067097055895963/50000000000000000000)
  directionLo := (110964074477859369433/25000000000000000000)
  directionHi := (443856297911437477733/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree080.table
  base := (9206878051878109333165635714278392283791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-58582587572649191256140069679624000000000000)
      constant := (1122284559637847918807621545653758498843345653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree080.table
  base := (9206864631670930852305244644491116189749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-58751742549659833833005165634624000000000000)
      constant := (1128717348290293644572561651956003878833498167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110964074477859369433/25000000000000000000)
  centralHi := (443856297911437477733/100000000000000000000)
  directionLo := (446656680883505999619/100000000000000000000)
  directionHi := (22332834044175299981/5000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree081.table
  base := (39414553956480670584932363957768674963/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-9885908585091300036734682984110250000000000)
      constant := (191874188849898516639843914817533178448315304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree081.table
  base := (2018022833418936526577871093721244996897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-19828906974923691943161335853033000000000000)
      constant := (385946604482349348286925366734191175344399085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446656680883505999619/100000000000000000000)
  centralHi := (22332834044175299981/5000000000000000000)
  directionLo := (224719807738488804039/50000000000000000000)
  directionHi := (449439615476977608079/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree082.table
  base := (10996250969361144790623018125897492949161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-60048315448446409184676126129699000000000000)
      constant := (1180578633329729490167459751369565219238941363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree082.table
  base := (10996240864820227373704879479497800049891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-60221699299882317825962849483574000000000000)
      constant := (1187337216965296596845392722456940054954031953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224719807738488804039/50000000000000000000)
  centralHi := (449439615476977608079/100000000000000000000)
  directionLo := (113051355957789396921/25000000000000000000)
  directionHi := (90441084766231517537/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree083.table
  base := (5962626245050098464136259830321892149981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-30390589693172509074472077177368250000000000)
      constant := (605142529605991155054285443298710029120304423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree083.table
  base := (11925243724003447733467525691992749844791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-60956677674993559822441691408049000000000000)
      constant := (1217209557761125121445800631582161007456908653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113051355957789396921/25000000000000000000)
  centralHi := (90441084766231517537/20000000000000000000)
  directionLo := (454954418293239837343/100000000000000000000)
  directionHi := (14217325571663744917/3125000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree084.table
  base := (12877129491509409185673932974231238302417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-20504681108081209037737394193258000000000000)
      constant := (413454803263082238818975735156967289527172537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree084.table
  base := (6438560943788465986737450195400072616579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-10281942675017466969820088888754000000000000)
      constant := (207909472484388268624830855864096051214585019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454954418293239837343/100000000000000000000)
  centralHi := (14217325571663744917/3125000000000000000)
  directionLo := (457686901830021370751/100000000000000000000)
  directionHi := (3575678920547041959/781250000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree085.table
  base := (6925940608300635199908714783800996567143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-31123453631071118038740105402405750000000000)
      constant := (635408342120852617311494531862765492954090869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree085.table
  base := (13851874621617055544072475117079980294347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-62426634425216043815399375256999000000000000)
      constant := (1278079047606070782367670378943262228033777801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457686901830021370751/100000000000000000000)
  centralHi := (3575678920547041959/781250000000000000)
  directionLo := (230201584208811970981/50000000000000000000)
  directionHi := (460403168417623941963/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree086.table
  base := (593980280674249765014200178498919027301/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-62979771200040845041748239029849000000000000)
      constant := (1301641881867011206636444571969826842039174575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree086.table
  base := (742475064883692866108952695001992964051/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-31580806400163642905939108590737000000000000)
      constant := (654538097589868662702779713810925302550672330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230201584208811970981/50000000000000000000)
  centralHi := (460403168417623941963/100000000000000000000)
  directionLo := (463103503410641855211/100000000000000000000)
  directionHi := (115775875852660463803/25000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree087.table
  base := (15870006336704267590606261162293595355497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-21237545045979818002005422418295500000000000)
      constant := (444280000687827418171854620266008382454584417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree087.table
  base := (7935000688818859081566154603295283829807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-10649431862573087968059509850991500000000000)
      constant := (223408046174092753888163830083667636525060327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463103503410641855211/100000000000000000000)
  centralHi := (115775875852660463803/25000000000000000000)
  directionLo := (93157636778405612117/20000000000000000000)
  directionHi := (232894091946014030293/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree088.table
  base := (16913378700227422578322819307762038262249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-64445499075838062970284295479924000000000000)
      constant := (1364411044315699272831066934281002037438015667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree088.table
  base := (8456687200389105698511865021547215943039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-32315784775274884902417950515212000000000000)
      constant := (686097646350778662027215060088809134866311237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93157636778405612117/20000000000000000000)
  centralHi := (232894091946014030293/50000000000000000000)
  directionLo := (58557184875616609361/12500000000000000000)
  directionHi := (468457479004932874889/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree089.table
  base := (3595924739953100183085326124259803347991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-65178363013736671934552323704961500000000000)
      constant := (1396355008182166256131510266134139143723121265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree089.table
  base := (3595923994528599248489961789703940285143/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-65366547925661011801314742954899000000000000)
      constant := (1404317241723547842515640848068390571019049345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58557184875616609361/12500000000000000000)
  centralHi := (468457479004932874889/100000000000000000000)
  directionLo := (235555825133810107233/50000000000000000000)
  directionHi := (471111650267620214467/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree090.table
  base := (762749639446074786445852227904589441741/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-21970408983878426966273450643333000000000000)
      constant := (476223964428245246980679480543835872836712525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree090.table
  base := (19068737755549549436143201060586809914171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-22033842100257417932597861626458000000000000)
      constant := (478938041248272635339498876562824650879015731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235555825133810107233/50000000000000000000)
  centralHi := (471111650267620214467/100000000000000000000)
  directionLo := (473750951872504292191/100000000000000000000)
  directionHi := (14804717246015759131/3125000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree091.table
  base := (20180730260346152008193212820910309262839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-66644090889533889863088380155036500000000000)
      constant := (1461361699299546999180357872624897267275404637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree091.table
  base := (315323866569390227471244783065341704593/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-33418252337941747897136213401924500000000000)
      constant := (734842969226159447870098926416458036801875008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473750951872504292191/100000000000000000000)
  centralHi := (14804717246015759131/3125000000000000000)
  directionLo := (95275126194054921239/20000000000000000000)
  directionHi := (119093907742568651549/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree092.table
  base := (21315591266263727464612973368916594650799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-67376954827432498827356408380074000000000000)
      constant := (1494424425949260386853681967066390609506815317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree092.table
  base := (2664448604988753752578173233836667788271/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-33785741525497368895375634364162000000000000)
      constant := (751466342789054384520538586171401319858789972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95275126194054921239/20000000000000000000)
  centralHi := (119093907742568651549/25000000000000000000)
  directionLo := (119746481985002024673/25000000000000000000)
  directionHi := (478985927940008098693/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree093.table
  base := (22473323784630729856302199734750617834643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-22703272921777035930541478868370500000000000)
      constant := (509286690998800768965152252059244461319556123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree093.table
  base := (22473321682223676803618202744628792908191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-22768820475368659929076703550933000000000000)
      constant := (512184788297626881554186297186514447364856951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119746481985002024673/25000000000000000000)
  centralHi := (478985927940008098693/100000000000000000000)
  directionLo := (481582076646104020459/100000000000000000000)
  directionHi := (24079103832305201023/5000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree094.table
  base := (11826963813858888772025260680923117165211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-34421341351614858377946232415074500000000000)
      constant := (780834320118830919495208704323082228077423513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree094.table
  base := (23653925806204550818599592889031357730081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-69041439801217221783708952577274000000000000)
      constant := (1570550976200419437296755789154717897921677723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481582076646104020459/100000000000000000000)
  centralHi := (24079103832305201023/5000000000000000000)
  directionLo := (484164304682818788871/100000000000000000000)
  directionHi := (60520538085352348609/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree095.table
  base := (24857402634826700176188825916538098004253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (468)
      previous := (234)
      next := (234)
      square := (2136694446450222023559106800000000000000)
      linear := (-192730046097308381496289454446500000000000)
      constant := (4420637472296406827278964752948266637762759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree095.table
  base := (6214350264211599498506826175022468349781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (234)
      previous := (117)
      next := (117)
      square := (1068347223225111011779553400000000000000)
      linear := (-96643238471369063407462319254500000000000)
      constant := (2222884375807276140975329095071189497598686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484164304682818788871/100000000000000000000)
  centralHi := (60520538085352348609/12500000000000000000)
  directionLo := (24336641680356225777/5000000000000000000)
  directionHi := (486732833607124515541/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree096.table
  base := (3260468583552817222969136605123408679089/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-11718068429837822447404753546704000000000000)
      constant := (271734089105245837036822553903012202132604516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree096.table
  base := (5216749460311634738068026380830174800721/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-23503798850479901925555545475408000000000000)
      constant := (546556331382195450926736519208406465515301405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24336641680356225777/5000000000000000000)
  centralHi := (486732833607124515541/100000000000000000000)
  directionLo := (3822561555941917887/781250000000000000)
  directionHi := (489287879160565489537/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree097.table
  base := (13666482805409257642196299449664204777961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-35520637258462771824348274752630750000000000)
      constant := (832665930753811767147959359096484581821406763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree097.table
  base := (5466592885389326046599204749706966607317/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-71246374926550947773145478350699000000000000)
      constant := (1674790400518813487053292601141027708553621555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3822561555941917887/781250000000000000)
  centralHi := (489287879160565489537/100000000000000000000)
  directionLo := (393463721184593089/80000000000000000)
  directionHi := (491829651480741361251/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree098.table
  base := (5721010672266982012062629395890742648061/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-71774138454824152612964577730299000000000000)
      constant := (1700632108018412261277585344666599355814250315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree098.table
  base := (5721010467212032720379750338556266565809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-71981353301662189769624320275174000000000000)
      constant := (1710286738344536189449672521679505120953855735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393463721184593089/80000000000000000)
  centralHi := (491829651480741361251/100000000000000000000)
  directionLo := (494358355303003743521/100000000000000000000)
  directionHi := (247179177651501871761/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree099.table
  base := (29900011833864050205844602586312659054443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-24169000797574253859077535318445500000000000)
      constant := (578768424690195531497364815726941358199903923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree099.table
  base := (29900010946027776060598644740131249251017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-24238777225591143922034387399883000000000000)
      constant := (582052669178001723140258108517053834104617137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494358355303003743521/100000000000000000000)
  centralHi := (247179177651501871761/50000000000000000000)
  directionLo := (248437095076457063459/50000000000000000000)
  directionHi := (496874190152914126919/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree100.table
  base := (15608920477391689235784720380012210172037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-36619933165310685270750317090187000000000000)
      constant := (886175679792206652219163423102046192366316071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree100.table
  base := (6243568037207300778075054806486767816867/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-73451310051884673762582004124124000000000000)
      constant := (1782404208010529987259223788302619597728334805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248437095076457063459/50000000000000000000)
  centralHi := (496874190152914126919/100000000000000000000)
  directionLo := (499377350529975120087/100000000000000000000)
  directionHi := (62422168816246890011/12500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree101.table
  base := (8139635165291706209559846316262676288007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-36986365134259989752884331202705750000000000)
      constant := (904385182245871728642718329286658158011698162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree101.table
  base := (16279269997799393916821421660473591850163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-37093144213497957879530423024299500000000000)
      constant := (909512669854301308144527746298245954661226529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499377350529975120087/100000000000000000000)
  centralHi := (62422168816246890011/12500000000000000000)
  directionLo := (100373605216622765039/20000000000000000000)
  directionHi := (125467006520778456299/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree102.table
  base := (33922110899251848476276287947751231682731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-24901864735472862823345563543483000000000000)
      constant := (615187429578117407104996916612701147762465891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree102.table
  base := (212013189519176404113485759031095112011/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-12486877800351192959256614662179000000000000)
      constant := (309336900428715000301624930980957433084877680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100373605216622765039/20000000000000000000)
  centralHi := (125467006520778456299/25000000000000000000)
  directionLo := (504346401778365417137/100000000000000000000)
  directionHi := (252173200889182708569/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree103.table
  base := (35308551623125608335837918342674349960107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-75438458144317197434304718855486500000000000)
      constant := (1882727132262515989670009984404369629600545881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree103.table
  base := (35308551124368099420909130132083121048347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-75656245177218399752018529897549000000000000)
      constant := (1893392396553857061538025395301330754470359801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504346401778365417137/100000000000000000000)
  centralHi := (252173200889182708569/50000000000000000000)
  directionLo := (506812658059176508983/100000000000000000000)
  directionHi := (63351582257397063623/12500000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree104.table
  base := (36717862793598946967232072857509804473483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-76171322082215806398572747080524000000000000)
      constant := (1920264895033792904832477705781642868244782089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree104.table
  base := (9179465590475550827560806428512864361137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-38195611776164820874248685911012000000000000)
      constant := (965569160806293550665430904075284364206222742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506812658059176508983/100000000000000000000)
  centralHi := (63351582257397063623/12500000000000000000)
  directionLo := (509266970999721469317/100000000000000000000)
  directionHi := (254633485499860734659/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree105.table
  base := (1192188886788792174363000778522943998701/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-12817364336685735893806795884260250000000000)
      constant := (326362596168662953213985206847383221802121976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree105.table
  base := (38150044003621814429621722564382930506187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-25708733975813627914992071248833000000000000)
      constant := (656419725904590451791435953699987316037733507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509266970999721469317/100000000000000000000)
  centralHi := (254633485499860734659/50000000000000000000)
  directionLo := (511709512451600341039/100000000000000000000)
  directionHi := (6396368905645004263/1250000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree106.table
  base := (39605096345553877011627615960624878275841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-77637049958013024327108803530599000000000000)
      constant := (1996459178166206081912555372605155352547735803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree106.table
  base := (39605096022226463884027288021225044137883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-77861180302552125741455055670974000000000000)
      constant := (2007754964827843415855059782876724160301327289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511709512451600341039/100000000000000000000)
  centralHi := (6396368905645004263/1250000000000000000)
  directionLo := (514140450184264242249/100000000000000000000)
  directionHi := (2056561800737056969/400000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree107.table
  base := (20541509337130179510728176490927436151349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-39184956947955816645688415877818250000000000)
      constant := (1017557849235093450173264668202139927023785967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree107.table
  base := (4108301839447931720226548431256079070469/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-39298079338831683868966948797724500000000000)
      constant := (1023312841464818895520406998686880472854089635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514140450184264242249/100000000000000000000)
  centralHi := (2056561800737056969/400000000000000000)
  directionLo := (103311989603898593647/20000000000000000000)
  directionHi := (129139987004873242059/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree108.table
  base := (42583811342699951738559594255022583783151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-26367592611270080751881619993558000000000000)
      constant := (691381712633848160224678483832464965245717511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree108.table
  base := (8516762220124149732045519756297767135787/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-26443712350924869911470913173308000000000000)
      constant := (695290443999251602090786922927882719680095535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103311989603898593647/20000000000000000000)
  centralHi := (129139987004873242059/25000000000000000000)
  directionLo := (518968165960229832033/100000000000000000000)
  directionHi := (259484082980114916017/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree109.table
  base := (44107474333306577605300154957779243842637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-79835641771708851219912888205711500000000000)
      constant := (2113547496441254760900152646721896760925325871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree109.table
  base := (5513434265483254942691010255311592299073/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-40033057713942925865445790722199500000000000)
      constant := (1062745956007008305589927273560935747527084236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518968165960229832033/100000000000000000000)
  centralHi := (259484082980114916017/50000000000000000000)
  directionLo := (260682630157030231581/50000000000000000000)
  directionHi := (521365260314060463163/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree110.table
  base := (45654007631162835364859299599432988423371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-80568505709607460184180916430749000000000000)
      constant := (2153322774073162195463746231541366160837510793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree110.table
  base := (1426687732811723354965183929640263751177/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-40400546901498546863685211684437000000000000)
      constant := (1082743711481500619874784978514269459030395056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260682630157030231581/50000000000000000000)
  centralHi := (521365260314060463163/100000000000000000000)
  directionLo := (130937845952901305973/25000000000000000000)
  directionHi := (523751383811605223893/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree111.table
  base := (5902926402952217630112951652089871819567/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-13550228274584344858074824109297750000000000)
      constant := (365578495130594294786407852925097878423079748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree111.table
  base := (9444682213376844000796978373976273630849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-27178690726036111907949755097783000000000000)
      constant := (735285954943881180049400214225866502028682445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130937845952901305973/25000000000000000000)
  centralHi := (523751383811605223893/100000000000000000000)
  directionLo := (263063342860039501461/50000000000000000000)
  directionHi := (526126685720079002923/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree112.table
  base := (3050980318747448796272464515153178698271/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-41017116792702339056358486440412000000000000)
      constant := (1116996043280432130659028263553148640241819944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree112.table
  base := (24407842482195004087292258106526818023037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-41135525276609788860164053608912000000000000)
      constant := (1123301618804446696690710025693682543918949071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263063342860039501461/50000000000000000000)
  centralHi := (526126685720079002923/100000000000000000000)
  directionLo := (528491311952257318689/100000000000000000000)
  directionHi := (52849131195225731869/10000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree113.table
  base := (50430829251133258762763206580598572141851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-82767097523303287076985001105861500000000000)
      constant := (2274886121395252304218972435454495624723374633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree113.table
  base := (25215414566939798382294986087122031876323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-41503014464165409858403474571149500000000000)
      constant := (1143861770642711506194663764632981152709557809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528491311952257318689/100000000000000000000)
  centralHi := (52849131195225731869/10000000000000000000)
  directionLo := (530845405171073827819/100000000000000000000)
  directionHi := (26542270258553691391/5000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree114.table
  base := (52068843669503840992001856156541947986499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (156)
      previous := (78)
      next := (78)
      square := (712231482150074007853035600000000000000)
      linear := (-77100610767499442328026804553000000000000)
      constant := (2138645498872077529246024355377995072986499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree114.table
  base := (52068843568098961612664241965378099231743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (156)
      previous := (78)
      next := (78)
      square := (712231482150074007853035600000000000000)
      linear := (-77323183105671340455480878178000000000000)
      constant := (2150709857667014117271648278900190599231743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530845405171073827819/100000000000000000000)
  centralHi := (26542270258553691391/5000000000000000000)
  directionLo := (133297276222515353457/25000000000000000000)
  directionHi := (533189104890061413829/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree115.table
  base := (26864864174323275251391669626421808265161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-42116412699550252502760528777968250000000000)
      constant := (1178896474101764820485690535092965863273044363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree115.table
  base := (26864864130477394068343069311419613862099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-42237992839276651854882316495624500000000000)
      constant := (1185544470653077081768292738127300371500153217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133297276222515353457/25000000000000000000)
  centralHi := (533189104890061413829/100000000000000000000)
  directionLo := (267761273784918479529/50000000000000000000)
  directionHi := (535522547569836959059/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree116.table
  base := (13853370820793073136763722030566100169851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-42482844668499556984894542890487000000000000)
      constant := (1199902870082312472500320683959462391717897266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree116.table
  base := (13853370801836196310993001756364524437593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-42605482026832272853121737457862000000000000)
      constant := (1206667018819115427365061150693409434931826438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267761273784918479529/50000000000000000000)
  centralHi := (535522547569836959059/100000000000000000000)
  directionLo := (67230733338852327051/12500000000000000000)
  directionHi := (537845866710818616409/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree117.table
  base := (57120108468576089141739716264838411526047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-28566184424965907644685704668670500000000000)
      constant := (814063817052288995035184370097961592342152967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree117.table
  base := (5712010840301241060755541655214223726229/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-14324323738129297950453719473366500000000000)
      constant := (409325677474166087874283486180486275388343345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67230733338852327051/12500000000000000000)
  centralHi := (537845866710818616409/100000000000000000000)
  directionLo := (270079596471176919573/50000000000000000000)
  directionHi := (540159192942353839147/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree118.table
  base := (11769920780221521221657929718964864971231/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-86431417212796331898325142231049000000000000)
      constant := (2484950081176194149370748623692953853194215865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree118.table
  base := (58849603844422508301912476432226461234729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-86680920803887029699201158764674000000000000)
      constant := (2498949022922622607215978949638266695017211507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270079596471176919573/50000000000000000000)
  centralHi := (540159192942353839147/100000000000000000000)
  directionLo := (542462654108426544293/100000000000000000000)
  directionHi := (271231327054213272147/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree119.table
  base := (60601969577660271969933571545973527257141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-87164281150694940862593170456086500000000000)
      constant := (2528081630219242020886884792123884763613233703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree119.table
  base := (60601969528654860914341685804554755227653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-87415899178998271695680000689149000000000000)
      constant := (2542318911867946499183000673620234034286548199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542462654108426544293/100000000000000000000)
  centralHi := (271231327054213272147/50000000000000000000)
  directionLo := (68094546918762816139/12500000000000000000)
  directionHi := (544756375350102529113/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree120.table
  base := (15594301373919082723572306684842112456201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-14649524181432258304476866446854000000000000)
      constant := (428597683047206758347915271627051630193377122) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree120.table
  base := (62377205453313087597099861874901628948057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-29383625851369837897386280871208000000000000)
      constant := (862021243892790974229553407354224488050248577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68094546918762816139/12500000000000000000)
  centralHi := (544756375350102529113/100000000000000000000)
  directionLo := (68380059898107948309/12500000000000000000)
  directionHi := (547040479184863586473/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree121.table
  base := (64175311653065551418240642672185400232623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-88630009026492158791129226906161500000000000)
      constant := (2615463485365926016298014539470670847045680709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree121.table
  base := (3208765580822334369239064168664919209187/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-44442927964610377844318842269049500000000000)
      constant := (1315091741175894742593711599415104442222995210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68380059898107948309/12500000000000000000)
  centralHi := (547040479184863586473/100000000000000000000)
  directionLo := (17166096424467894753/3125000000000000000)
  directionHi := (549315085582972632097/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree122.table
  base := (32998144024067819021227138311172783533293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-44681436482195383877698627565599500000000000)
      constant := (1329856895732732831746337647240478304254056319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree122.table
  base := (65996288016484342281023873677717021907943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-89620834304331997685116526462574000000000000)
      constant := (2674678163886494449289229474941183972226302269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17166096424467894753/3125000000000000000)
  centralHi := (549315085582972632097/100000000000000000000)
  directionLo := (551580312041004527067/100000000000000000000)
  directionHi := (137895078010251131767/25000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree123.table
  base := (67840134679532671676891928711756713219697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-30031912300763125573221761118745500000000000)
      constant := (901445672193464399098987508108397724253560617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree123.table
  base := (678401346521768646651219904022415240957/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-15059302113240539946932561397841500000000000)
      constant := (453257962713522490800142473281941946661773850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551580312041004527067/100000000000000000000)
  centralHi := (137895078010251131767/25000000000000000000)
  directionLo := (22153450946106804697/4000000000000000000)
  directionHi := (276918136826335058713/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree124.table
  base := (13941370309238028798352948876878768729813/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-90828600840187985683933311581274000000000000)
      constant := (2749333160709553589189714899519205470171937395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree124.table
  base := (2178339110079637654607116270870837734631/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-45545395527277240839037105155762000000000000)
      constant := (1382396159767327063308355301716824751265685968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22153450946106804697/4000000000000000000)
  centralHi := (276918136826335058713/50000000000000000000)
  directionLo := (17377596349282946467/3125000000000000000)
  directionHi := (111216616635410857389/20000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree125.table
  base := (71596438647285355667792211014149189363743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-91561464778086594648201339806311500000000000)
      constant := (2794702223852055855808151624888918786924683669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree125.table
  base := (71596438626854733650864587605952618820361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-91825769429665723674553052235999000000000000)
      constant := (2810411793646245994213122941718440045557450963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17377596349282946467/3125000000000000000)
  centralHi := (111216616635410857389/20000000000000000000)
  directionLo := (139580212776095624881/25000000000000000000)
  directionHi := (22332834044175299981/4000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree126.table
  base := (3675444799110106210995756959196917491289/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-15382388119330867268744894671891500000000000)
      constant := (473407367667872111920158933049271786206053290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree126.table
  base := (73508895964547581959129454631827220845489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-30853582601592321890343964720158000000000000)
      constant := (952135399538438924154011852541607939225221529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139580212776095624881/25000000000000000000)
  centralHi := (22332834044175299981/4000000000000000000)
  directionLo := (560549685719424366321/100000000000000000000)
  directionHi := (280274842859712183161/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree127.table
  base := (1178815992976545276059724481598198648699/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-46513596326941906288368698128193250000000000)
      constant := (1443279553587302917766721915607966045416187544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree127.table
  base := (75444223535244170315051871681736385128313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-93295726179888207667510736084949000000000000)
      constant := (2902775534441451911103032853733754989468962979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560549685719424366321/100000000000000000000)
  centralHi := (280274842859712183161/50000000000000000000)
  directionLo := (562769693162637184479/100000000000000000000)
  directionHi := (3517310582266482403/625000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree128.table
  base := (38701210675940749712981121039559620810719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-46880028295891210770502712240712000000000000)
      constant := (1466523463676928377301734942348099069338008677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree128.table
  base := (38701210669350589678795135800204113431179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-47015352277499724831994789004712000000000000)
      constant := (1474759900562193947634053406408037054845966857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562769693162637184479/100000000000000000000)
  centralHi := (3517310582266482403/625000000000000000)
  directionLo := (564980977489147135453/100000000000000000000)
  directionHi := (282490488744573567727/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree129.table
  base := (3175339575447193618189796806487535569927/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-31497640176560343501757817568820500000000000)
      constant := (993302555514933740767051985608806090549841175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree129.table
  base := (79383489374792524336680835603888208025491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-31588560976703563886822806644633000000000000)
      constant := (998879666221329391724312773042919471222202251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564980977489147135453/100000000000000000000)
  centralHi := (282490488744573567727/50000000000000000000)
  directionLo := (283591820362830439761/50000000000000000000)
  directionHi := (567183640725660879523/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree130.table
  base := (40693713826664014792295920864947497991723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-47612892233789819734770740465749500000000000)
      constant := (1513570662373683939244924233919821382512536009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree130.table
  base := (16277485528698077139573936696445997146199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-95500661305221933656947261858374000000000000)
      constant := (3044133127060222622240053820404436012046667585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283591820362830439761/50000000000000000000)
  centralHi := (567183640725660879523/100000000000000000000)
  directionLo := (569377782925395619143/100000000000000000000)
  directionHi := (71172222865674452393/12500000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree131.table
  base := (83414236153347394250774720768168695942471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-95958648405478248433809509156536500000000000)
      constant := (3074747901961579820781946683982633412549446093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree131.table
  base := (4170711807242451348674847273279489018327/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-48117819840166587826713051891424500000000000)
      constant := (1546001093156575001937488838841183045755981410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569377782925395619143/100000000000000000000)
  centralHi := (71172222865674452393/12500000000000000000)
  directionLo := (571563502221111308321/100000000000000000000)
  directionHi := (285781751110555654161/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree132.table
  base := (42731957443165996796476846943162773120071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-16115252057229476233012922896929000000000000)
      constant := (520454566364589819204283755533879917346345631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree132.table
  base := (85463914878990998330663205447547180046821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-32323539351814805883301648569108000000000000)
      constant := (1046748725474301013969559941106431781996902381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571563502221111308321/100000000000000000000)
  centralHi := (285781751110555654161/50000000000000000000)
  directionLo := (286870447438162270483/50000000000000000000)
  directionHi := (573740894876324540967/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree133.table
  base := (17507292770487253127252131265839025747561/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (468)
      previous := (234)
      next := (234)
      square := (2136694446450222023559106800000000000000)
      linear := (-269873618507688272471871372871500000000000)
      constant := (8784154607826627197236381878259643979963415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree133.table
  base := (43768231923047690858045411553463830157151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (234)
      previous := (117)
      next := (117)
      square := (1068347223225111011779553400000000000000)
      linear := (-135326310845644957958980315279500000000000)
      constant := (4416710661204536955802576970702758677971453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286870447438162270483/50000000000000000000)
  centralHi := (573740894876324540967/100000000000000000000)
  directionLo := (143977513833694935491/25000000000000000000)
  directionHi := (115182011066955948393/20000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree134.table
  base := (44815941525932250750673570620316138801229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-49078620109587037663306796915824500000000000)
      constant := (1609902573837710788497753134461392058009231007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree134.table
  base := (44815941523193891440941234130425900601927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-49220287402833450821431314778137000000000000)
      constant := (1618929474606856127723423558839298469101886941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143977513833694935491/25000000000000000000)
  centralHi := (115182011066955948393/20000000000000000000)
  directionLo := (115614215253649919111/20000000000000000000)
  directionHi := (144517769067062398889/25000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree135.table
  base := (91750172484861883506872894714779328857927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-32963368052357561430293874018895500000000000)
      constant := (1089634466979277308018776090278797857248961647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree135.table
  base := (3670006899205272714177281986071275989703/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-33058517726926047879780490493583000000000000)
      constant := (1095742577298432752712474686993665843932069575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115614215253649919111/20000000000000000000)
  centralHi := (144517769067062398889/25000000000000000000)
  directionLo := (29011202431136658127/5000000000000000000)
  directionHi := (580224048622733162541/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree136.table
  base := (46945666075853430836722726985091859419119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-49811484047485646627574825140862000000000000)
      constant := (1659187286606472510378558913300123358750905877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree136.table
  base := (46945666073810938816366164062078317431409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-49955265777944692817910156702612000000000000)
      constant := (1668485722717376257806550281374560317778215947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29011202431136658127/5000000000000000000)
  centralHi := (580224048622733162541/100000000000000000000)
  directionLo := (291184530831558423979/50000000000000000000)
  directionHi := (582369061663116847959/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree137.table
  base := (96055362052704675408001191076988696512273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-100355832032869902219417678506761500000000000)
      constant := (3368218664501091441375587027166308691916541659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree137.table
  base := (48027681024588492969320244053156924046839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-50322754965500313816149577664849500000000000)
      constant := (1693545044916210265282323976859428065930226637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291184530831558423979/50000000000000000000)
  centralHi := (582369061663116847959/100000000000000000000)
  directionLo := (23380248120654410883/4000000000000000000)
  directionHi := (146126550754090068019/25000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree138.table
  base := (98242262188181854809268520552623599650109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-33696231990256170394561902243933000000000000)
      constant := (1139478558267541606002886248485651822598689349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree138.table
  base := (49121131092567795716425660080891637707339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-16896748051018644938129666209029000000000000)
      constant := (572930610848111473815266448678417787462349379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23380248120654410883/4000000000000000000)
  centralHi := (146126550754090068019/25000000000000000000)
  directionLo := (293317779356633079313/50000000000000000000)
  directionHi := (586635558713266158627/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree139.table
  base := (25113008139620389936498296263247959216683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-50910779954333560073976867478418250000000000)
      constant := (1734512802058958396397092310384265218335210378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree139.table
  base := (20090406511170231718528974154283015437411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-102115466681223111625256839178649000000000000)
      constant := (3488452171203880254622847068142833137968580565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293317779356633079313/50000000000000000000)
  centralHi := (586635558713266158627/100000000000000000000)
  directionLo := (588757213228890574811/100000000000000000000)
  directionHi := (147189303307222643703/25000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree140.table
  base := (51342336581979817591940883372093951972189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-51277211923282864556110881590937000000000000)
      constant := (1759994226223676372915012440793456968735880687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree140.table
  base := (12835584145211055120763843325279097534797/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-51425222528167176810867840551562000000000000)
      constant := (1769847804089224896925487062978110925520740604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588757213228890574811/100000000000000000000)
  centralHi := (147189303307222643703/25000000000000000000)
  directionLo := (59087124952164722777/10000000000000000000)
  directionHi := (590871249521647227771/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree141.table
  base := (20988036800996255731622153610454845999/2000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-17214547964077389679414965234485250000000000)
      constant := (595220703298554697674462613339921930154722500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree141.table
  base := (104940184003020337239663621924385979192191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-34528474477148531872738174342533000000000000)
      constant := (1197104658670927103284455652581748291613380951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59087124952164722777/10000000000000000000)
  centralHi := (590871249521647227771/100000000000000000000)
  directionLo := (592977749071157033171/100000000000000000000)
  directionHi := (148244437267789258293/25000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree142.table
  base := (53609282540959115360074751864002403663323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-52010075861181473520378909815974500000000000)
      constant := (1811516453075122854230839142000724970354878809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree142.table
  base := (6701160317514077805097050235755969309247/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-52160200903278418807346682476037000000000000)
      constant := (1821653637353642303544069781513981686845316008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592977749071157033171/100000000000000000000)
  centralHi := (148244437267789258293/25000000000000000000)
  directionLo := (595076791914891814611/100000000000000000000)
  directionHi := (148769197978722953653/25000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree143.table
  base := (6844988524696650749113370797168258482363/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-52376507830130778002512923928493250000000000)
      constant := (1837557255762256217550830688525798227038068032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree143.table
  base := (109519816393684838396742830705970115267357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-105055380181668079611172206876549000000000000)
      constant := (3695675504262373039044168537065516619209547631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595076791914891814611/100000000000000000000)
  centralHi := (148769197978722953653/25000000000000000000)
  directionLo := (119433691336731751969/20000000000000000000)
  directionHi := (298584228341829379923/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree144.table
  base := (5592196897252197069023371018544877730167/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-17580979933026694161548979347004000000000000)
      constant := (621261505985756311460482247290555508605902870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree144.table
  base := (111843937943782209741922691118016541250161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-35263452852259773869217016267008000000000000)
      constant := (1249472888226153831436849351428815971391308121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119433691336731751969/20000000000000000000)
  centralHi := (298584228341829379923/50000000000000000000)
  directionLo := (119850564127194028821/20000000000000000000)
  directionHi := (299626410317985072053/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree145.table
  base := (114190929731989479578214537165129702321099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-106218743536058773933561904307061500000000000)
      constant := (3780396479320732098955429854024014588707500217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree145.table
  base := (3568466554090634920479565254795870845479/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-53262668465945281802064945362749500000000000)
      constant := (1900768377977982358492103437598522342197960112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119850564127194028821/20000000000000000000)
  centralHi := (299626410317985072053/50000000000000000000)
  directionLo := (300664979845670412511/50000000000000000000)
  directionHi := (601329959691340825023/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree146.table
  base := (116560791756360849688638344969294551371697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-106951607473957382897829932532099000000000000)
      constant := (3833596841743504308106948943857595233510547851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree146.table
  base := (116560791755420698770529163123532396915161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-107260315307001805600608732649974000000000000)
      constant := (3855029778095295911889042980837345523359119363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300664979845670412511/50000000000000000000)
  centralHi := (601329959691340825023/100000000000000000000)
  directionLo := (37712496778909631967/6250000000000000000)
  directionHi := (603399948462554111473/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree147.table
  base := (14869190502316736768626456320519919054423/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-17947411901975998643682993459522750000000000)
      constant := (647861687197210255596169533831274319755211812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree147.table
  base := (118953524017722405590465379539807686939977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-35998431227371015865695858191483000000000000)
      constant := (1302965910365621864078666097396803528110331697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37712496778909631967/6250000000000000000)
  centralHi := (603399948462554111473/100000000000000000000)
  directionLo := (605462860286934804039/100000000000000000000)
  directionHi := (15136571507173370101/2500000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree148.table
  base := (60684563259440766348243260688525196562833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-54208667674877300413182994491087000000000000)
      constant := (1970558161820203823720485160218980506627548139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree148.table
  base := (121369126518181130858425252284438303507049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-108730272057224289593566416498924000000000000)
      constant := (3963140614961080633482634776873602432698134067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605462860286934804039/100000000000000000000)
  centralHi := (15136571507173370101/2500000000000000000)
  directionLo := (303759383628333246047/50000000000000000000)
  directionHi := (121503753451333298419/20000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree149.table
  base := (15475949907221623920572013175839062533401/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-54575099643826604895317008603605750000000000)
      constant := (1997717721557671260746551517745590582566568132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree149.table
  base := (123807599257168496708379077893558047581467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-109465250432335531590045258423399000000000000)
      constant := (4017758429688343502400042266035553974905728761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303759383628333246047/50000000000000000000)
  centralHi := (121503753451333298419/20000000000000000000)
  directionLo := (609567740248188566411/100000000000000000000)
  directionHi := (152391935062047141603/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree150.table
  base := (126268942235573176792204374953417965712991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-36627687741850606251634015144083000000000000)
      constant := (1350042493869487116541123336716167088747389751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree150.table
  base := (126268942235051479928969046329197277320973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-36733409602482257862174700115958000000000000)
      constant := (1357583725093017211616773417135048029612871253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609567740248188566411/100000000000000000000)
  centralHi := (152391935062047141603/25000000000000000000)
  directionLo := (3822561555941917887/625000000000000000)
  directionHi := (611609848950706861921/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree151.table
  base := (128753155452642173855374122876316372923023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-110615927163450427719170073657286500000000000)
      constant := (4105192439120154103752482269076380315469383909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree151.table
  base := (64376577726095976914733236229250033520423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-55467603591279007791501471136174500000000000)
      constant := (2064059425866798469813704783491744903490118109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3822561555941917887/625000000000000000)
  centralHi := (611609848950706861921/100000000000000000000)
  directionLo := (613645161893850377931/100000000000000000000)
  directionHi := (153411290473462594483/25000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree152.table
  base := (32815059727333711954990035375885235391169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (234)
      previous := (117)
      next := (117)
      square := (1068347223225111011779553400000000000000)
      linear := (-154222702356439108979831166042000000000000)
      constant := (5762645866552361638453437967266186412347014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree152.table
  base := (65630119454473164319857380387263753519299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (234)
      previous := (117)
      next := (117)
      square := (1068347223225111011779553400000000000000)
      linear := (-154667847032782905234739313292000000000000)
      constant := (5794821965446489486163754321103291260557897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613645161893850377931/100000000000000000000)
  centralHi := (153411290473462594483/25000000000000000000)
  directionLo := (307836873237252564343/50000000000000000000)
  directionHi := (615673746474505128687/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree153.table
  base := (66895096303000267472729761569400793953281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-18680275839874607607951021684560250000000000)
      constant := (702740185200132113070850865163806321382759441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree153.table
  base := (133790192605665275181885954486148967976337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-37468387977593499858653542040433000000000000)
      constant := (1413326332411912273166398577586536355564457657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307836873237252564343/50000000000000000000)
  centralHi := (615673746474505128687/100000000000000000000)
  directionLo := (154423917245713712823/25000000000000000000)
  directionHi := (617695668982854851293/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree154.table
  base := (68171508271491403904519209085296181689261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-56407259488573127305987079166199500000000000)
      constant := (2136312412885244459619361072898536694456969663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree154.table
  base := (136343016542693518782697485616356893830491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-113140142307891741572439468045774000000000000)
      constant := (4296471466284084508623139884633488953518421753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154423917245713712823/25000000000000000000)
  centralHi := (617695668982854851293/100000000000000000000)
  directionLo := (309855497313828518599/50000000000000000000)
  directionHi := (619710994627657037199/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree155.table
  base := (138918710720619303622896792594358126660043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-113547382915044863576242186557436500000000000)
      constant := (4329181459360259486505045639981959753516576569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree155.table
  base := (34729677680092423076074117557474911029423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-56937560341501491784459154985124500000000000)
      constant := (2176669433098887607885884201078169211977230218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309855497313828518599/50000000000000000000)
  centralHi := (619710994627657037199/100000000000000000000)
  directionLo := (155429946890195388443/25000000000000000000)
  directionHi := (621719787560781553773/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree156.table
  base := (70758637569620802766915365102488062983641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-19046707808823912090085035797079000000000000)
      constant := (731018501995077247462009305381224846987094401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree156.table
  base := (141517275139026238806378196868799294335143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-38203366352704741855132383964908000000000000)
      constant := (1470193732325722992259577094273055795254986623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155429946890195388443/25000000000000000000)
  centralHi := (621719787560781553773/100000000000000000000)
  directionLo := (124744422180207596177/20000000000000000000)
  directionHi := (311861055450518990443/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree157.table
  base := (36034677449793792090763785564743115723043/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-57506555395421040752389121503755750000000000)
      constant := (2221706741800726690805564235802029571077986138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree157.table
  base := (144138709798989355750726799438625559948889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-115345077433225467561875993819199000000000000)
      constant := (4468198458622619063495140743641707840799646787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124744422180207596177/20000000000000000000)
  centralHi := (311861055450518990443/50000000000000000000)
  directionLo := (156429506689329175151/25000000000000000000)
  directionHi := (125143605351463340121/20000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree158.table
  base := (29356602940147856300426821814293354262209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-115745974728740690469046271232549000000000000)
      constant := (4501088874253574967433327456913364497704861735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree158.table
  base := (146783014700578973856063348460641580270381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-116080055808336709558354835743674000000000000)
      constant := (4526190651134471960889371703998487768932822623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156429506689329175151/25000000000000000000)
  centralHi := (125143605351463340121/20000000000000000000)
  directionLo := (313853798125533871527/50000000000000000000)
  directionHi := (125541519250213548611/20000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree159.table
  base := (74725094922123531378745695273667217835861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-19413139777773216572219049909597750000000000)
      constant := (759856197321194558137168286698707531654370821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree159.table
  base := (149450189844108764734832304535022278023127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-38938344727815983851611225889383000000000000)
      constant := (1528185924837689125105900504906498870491348847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313853798125533871527/50000000000000000000)
  centralHi := (125541519250213548611/20000000000000000000)
  directionLo := (125938175907628081119/20000000000000000000)
  directionHi := (157422719884535101399/25000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree160.table
  base := (76070117615002738928681163013078445697803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-58605851302268954198791163841312000000000000)
      constant := (2308779206311281484831927066972733956690720649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree160.table
  base := (30428047045977234463835062457667535706847/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-117550012558559193551312519592624000000000000)
      constant := (4643299828758738268558639576935309705852576505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125938175907628081119/20000000000000000000)
  centralHi := (157422719884535101399/25000000000000000000)
  directionLo := (315833967915002861461/50000000000000000000)
  directionHi := (631667935830005722923/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree161.table
  base := (154853150858315381123421717907416074671863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-117944566542436517361850355907661500000000000)
      constant := (4676352560340087655186234509171671604963377629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree161.table
  base := (15485315085821246383210084067007762385813/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-59142495466835217773895680758549500000000000)
      constant := (2351208406935905456507352031259112275506677395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315833967915002861461/50000000000000000000)
  centralHi := (631667935830005722923/100000000000000000000)
  directionLo := (633638823414382970197/100000000000000000000)
  directionHi := (316819411707191485099/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree162.table
  base := (78794468364735786741864087820164542115517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-19779571746722521054353064022116500000000000)
      constant := (789253271180010112465873053317393063766201637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree162.table
  base := (15758893672938279669998185580464787220929/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-19836661551463612924045033906929000000000000)
      constant := (793651454975434160696442815630162097183776845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633638823414382970197/100000000000000000000)
  centralHi := (316819411707191485099/50000000000000000000)
  directionLo := (127120719935058105477/20000000000000000000)
  directionHi := (317801799837645263693/50000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree163.table
  base := (160347592843762874580391385120560403708527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-119410294418233735290386412357736500000000000)
      constant := (4795059612842794820163270355968532882060084741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree163.table
  base := (40086898210921574587403530655052206703307/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-59877473841946459770374522683024500000000000)
      constant := (2410887788350716773526858942070375759406862962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127120719935058105477/20000000000000000000)
  centralHi := (317801799837645263693/50000000000000000000)
  directionLo := (637562321112540618613/100000000000000000000)
  directionHi := (318781160556270309307/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree164.table
  base := (81564559600736103109244962742930282427337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-60071579178066172127327220291387000000000000)
      constant := (2427486258814298247802615359285189464618805971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree164.table
  base := (20391139900175769537565052072539517719477/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-60244963029502080768613943645262000000000000)
      constant := (2441008677209301676861765099712296065760774364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637562321112540618613/100000000000000000000)
  centralHi := (318781160556270309307/50000000000000000000)
  directionLo := (127903008672139332667/20000000000000000000)
  directionHi := (79939380420087082917/12500000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree165.table
  base := (82966757901438342412119755750343604973441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (128557782528088358417472925800000000000000)
      linear := (-20146003715671825536487078134635250000000000)
      constant := (819209723572960969701785171133300691786037201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree165.table
  base := (165933515802819716362450107474652066450791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-40408301478038467844568909738333000000000000)
      constant := (1647544687668138249900017469038240099113735551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127903008672139332667/20000000000000000000)
  centralHi := (79939380420087082917/12500000000000000000)
  directionLo := (64146182120751123459/10000000000000000000)
  directionHi := (641461821207511234591/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree166.table
  base := (84380391324123860470258159372787318047043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-60804443115964781091595248516424500000000000)
      constant := (2487958542135298362798823089405263595132447569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree166.table
  base := (168760782648198587088915754369045424917333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-121959882809226645530185571139474000000000000)
      constant := (5003625702459161887046738608679428632685471639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64146182120751123459/10000000000000000000)
  centralHi := (641461821207511234591/100000000000000000000)
  directionLo := (128680541722372382357/20000000000000000000)
  directionHi := (321701354305930955893/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree167.table
  base := (171610919737851124095389614485131062503059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-122341750169828171147458525257886500000000000)
      constant := (5036948746127377089484935191050118749284562897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree167.table
  base := (42902729934452187232134523365307334859813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-61347430592168943763332206531974500000000000)
      constant := (2532496136391566411294722530710431054493854958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128680541722372382357/20000000000000000000)
  centralHi := (321701354305930955893/50000000000000000000)
  directionLo := (645337758721201639503/100000000000000000000)
  directionHi := (40333609920075102469/6250000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree168.table
  base := (174483927071947211641864556508006532710613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-41024871369242260037242184494308000000000000)
      constant := (1699451109002796277855294216467895608308531293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree168.table
  base := (174483927071910666764141635622555088104903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (257115565056176716834945851600000000000000)
      linear := (-41143279853149709841047751662808000000000000)
      constant := (1708911257992203213265423570204231386805869983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell035.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645337758721201639503/100000000000000000000)
  centralHi := (40333609920075102469/6250000000000000000)
  directionLo := (647267023888539558241/100000000000000000000)
  directionHi := (323633511944269779121/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree169.table
  base := (177379804650790920391052142938223786504711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (771346695168530150504837554800000000000000)
      linear := (-123807478045625389075994581707961500000000000)
      constant := (5160130826913908054406921764839548044378352013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree169.table
  base := (22172475581344925592640675792033321069423/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (385673347584265075252418777400000000000000)
      linear := (-62082408967280185759811048456449500000000000)
      constant := (2594425103019934286568341350426638964060240436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell035.Kernel169
