import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell102.Parameters
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch000_049
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch050_099
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch100_149
import ForestUnimodality.BinomialMassData.Q11311_21736.Batch000_049
import ForestUnimodality.BinomialMassData.Q11311_21736.Batch050_099
import ForestUnimodality.BinomialMassData.Q11311_21736.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree000.table
  base := (2545642409371576150356020209/50000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (102)
      previous := (51)
      next := (51)
      square := (914287988384543531816817110000000000000)
      linear := (-42669862672434933498211151000000000000)
      constant := (509128481874315230071204041800000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree000.table
  base := (2545642409371576150356020209/50000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (102)
      previous := (51)
      next := (51)
      square := (914287988384543531816817110000000000000)
      linear := (-42669862672434933498211151000000000000)
      constant := (509128481874315230071204041800000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree001.table
  base := (142380602715941211363487097486015028360181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-563977037748984670465397795859556750000000000)
      constant := (161855381572785013582591361415120788478515222786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree001.table
  base := (56902807220159804886323332272389540972339/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-43428783237799871189201204194963500000000000)
      constant := (12439642325525058935523110245923002914813699295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9991688896166689071/20000000000000000000)
  directionHi := (12489611120208361339/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree002.table
  base := (16693776286789813245225726171976869945539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-1103723865969839146639035894990310500000000000)
      constant := (95382426587103809523132409953500018635591577670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree002.table
  base := (166679232055090625557576687964302327849843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-1104918154654666456627471612340248000000000000)
      constant := (95236889241522384582092354345436548901516897079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9991688896166689071/20000000000000000000)
  centralHi := (12489611120208361339/25000000000000000000)
  directionLo := (35325954869928977883/50000000000000000000)
  directionHi := (70651909739857955767/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree003.table
  base := (103655322126518163859577618879963426794881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-1643470694190693622812673994121064250000000000)
      constant := (60161306669324620279882379323270667787941060493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree003.table
  base := (51724223908893565698215514393880197360533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-1645262127217934587795327570145970500000000000)
      constant := (60046669413066685463193975476847997267291491298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35325954869928977883/50000000000000000000)
  centralHi := (70651909739857955767/100000000000000000000)
  directionLo := (43265282053956244873/50000000000000000000)
  directionHi := (86530564107912489747/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree004.table
  base := (68498136927702414340433408990369700020451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-2183217522411548098986312093251818000000000000)
      constant := (41191761047087833466295664258924787890713161703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree004.table
  base := (68346567726958597926227626992538367180333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-2185606099781202718963183527951693000000000000)
      constant := (41110716892484764302407755258591781418453635049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43265282053956244873/50000000000000000000)
  centralHi := (86530564107912489747/100000000000000000000)
  directionLo := (99916888961666890711/100000000000000000000)
  directionHi := (12489611120208361339/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree005.table
  base := (24009101814014706562958501012050969078339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-209458796202492505781534630183274750000000000)
      constant := (2372100039035818203218135409754255471559351718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree005.table
  base := (1197741740807264158670845045862401999759/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-2725950072344470850131039485757415500000000000)
      constant := (30783503094954104726701950532065676104515897080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99916888961666890711/100000000000000000000)
  centralHi := (12489611120208361339/12500000000000000000)
  directionLo := (11171047790929277323/10000000000000000000)
  directionHi := (111710477909292773231/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree006.table
  base := (35340127690622991043880540497618799573059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-3262711178853257051333588291513325500000000000)
      constant := (25193711636509286513590990211310866037710272327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree006.table
  base := (7052278440507945663435440363158435469707/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-3266294044907738981298895443563138000000000000)
      constant := (25160265609444200364673603282165973908897645355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11171047790929277323/10000000000000000000)
  centralHi := (111710477909292773231/100000000000000000000)
  directionLo := (61186348660602199773/50000000000000000000)
  directionHi := (122372697321204399547/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree007.table
  base := (26928735803031665348012859996628543517997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-3802458007074111527507226390644079250000000000)
      constant := (22253535663223271249620320266292614752012650441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree007.table
  base := (16793509970246571760874428202632942533/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-3806638017471007112466751401368860500000000000)
      constant := (22235279789862420813688867394601545999656638400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61186348660602199773/50000000000000000000)
  centralHi := (122372697321204399547/100000000000000000000)
  directionLo := (33044404995978161963/25000000000000000000)
  directionHi := (132177619983912647853/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree008.table
  base := (5236892112968839337810491479165314675597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-4342204835294966003680864489774833000000000000)
      constant := (20973933543556173027233857139618514737927132964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree008.table
  base := (20901186966392587478092196657248122314681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-4346981990034275243634607359174583000000000000)
      constant := (20967583685851730843664724837647037000758549893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33044404995978161963/25000000000000000000)
  centralHi := (132177619983912647853/100000000000000000000)
  directionLo := (141303819479715911533/100000000000000000000)
  directionHi := (70651909739857955767/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree009.table
  base := (8213658015816655282061708569241537403979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-4881951663515820479854502588905586750000000000)
      constant := (20804479910084213711631106608408255033610874174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree009.table
  base := (4097333784425770976923152190126648618861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-4887325962597543374802463316980305500000000000)
      constant := (20808193991937904752964424600973085536414301732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141303819479715911533/100000000000000000000)
  centralHi := (70651909739857955767/50000000000000000000)
  directionLo := (149875333442500336067/100000000000000000000)
  directionHi := (37468833360625084017/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree010.table
  base := (3210951954128299140650808490534592137261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-5421698491736674956028140688036340500000000000)
      constant := (21447522843654042230227744138102935089430282532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree010.table
  base := (1281159606882091676108751031599370319691/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-5427669935160811505970319274786028000000000000)
      constant := (21460427732604486177403621552793205466474934230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149875333442500336067/100000000000000000000)
  centralHi := (37468833360625084017/25000000000000000000)
  directionLo := (78991236459250935969/50000000000000000000)
  directionHi := (157982472918501871939/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree011.table
  base := (1237928012160290307993402808472891574569/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-49268143140144871340510568488984250000000000)
      constant := (187903549681973109351111648832540295963118536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree011.table
  base := (9875414432627135446520443336613791676003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-49322428989455203612712192004890500000000000)
      constant := (188083937914718988980178807898852618085482079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78991236459250935969/50000000000000000000)
  centralHi := (157982472918501871939/100000000000000000000)
  directionLo := (82846707726363054179/50000000000000000000)
  directionHi := (165693415452726108359/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree012.table
  base := (7433658732622342079508240492423253744733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-6501192148178383908375416886297848000000000000)
      constant := (24572941783812278877139557101628881033707868249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree012.table
  base := (1852229008520069398493985341785269180047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-6508357880287347768306031190397473000000000000)
      constant := (24603780979890559689358074536877642838788916364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82846707726363054179/50000000000000000000)
  centralHi := (165693415452726108359/100000000000000000000)
  directionLo := (43265282053956244873/25000000000000000000)
  directionHi := (173061128215824979493/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree013.table
  base := (5327035341610421266271978790143837727473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-541610690492249106503773460417584750000000000)
      constant := (2068948375015266617736906336042841561711248113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree013.table
  base := (1060997228033928920633725481379109952577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-542207834834662761497991319092553500000000000)
      constant := (2072036598980680616415775823859652977942579685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43265282053956244873/25000000000000000000)
  centralHi := (173061128215824979493/100000000000000000000)
  directionLo := (22515966652258240663/12500000000000000000)
  directionHi := (36025546643613185061/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree014.table
  base := (14048551170709723807919336858538649423/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-7580685804620092860722693084559355500000000000)
      constant := (29665936921117383040735920737079855016449704750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree014.table
  base := (3492409682296741879942713910495342473983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-583772755801068002357057162000686000000000000)
      constant := (2285830862915923206766732526972844179606051423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22515966652258240663/12500000000000000000)
  centralHi := (36025546643613185061/20000000000000000000)
  directionLo := (93463691411723151997/50000000000000000000)
  directionHi := (37385476564689260799/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree015.table
  base := (121153508370075648485107529549344600423/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-8120432632840947336896331183690109250000000000)
      constant := (32853083693851532213065611095398382224831529104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree015.table
  base := (1920786133271930920918609901446503952223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-8129389797977152161809599063814640500000000000)
      constant := (32913137182798802919985775083517080202531687219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93463691411723151997/50000000000000000000)
  centralHi := (37385476564689260799/20000000000000000000)
  directionLo := (48372055869173943751/25000000000000000000)
  directionHi := (38697644695339155001/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree016.table
  base := (568302127692547266949769560825903584019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-8660179461061801813069969282820863000000000000)
      constant := (36436367814587095412033292593960624827895941207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree016.table
  base := (552486279779417215861818336803728957119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-8669733770540420292977455021620363000000000000)
      constant := (36507115819755237849439652559458185899486895507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48372055869173943751/25000000000000000000)
  centralHi := (38697644695339155001/20000000000000000000)
  directionLo := (99916888961666890711/50000000000000000000)
  directionHi := (199833777923333781423/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree017.table
  base := (-627632177049829546484613895409482675749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-9199926289282656289243607381951616750000000000)
      constant := (40399146675401433678789011263767500463815403103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree017.table
  base := (-10027585498166202148457790861908926253/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-9210077743103688424145310979426085500000000000)
      constant := (40481112895065936831579963214809376395779132224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99916888961666890711/50000000000000000000)
  centralHi := (199833777923333781423/100000000000000000000)
  directionLo := (1287399646787699647/625000000000000000)
  directionHi := (205983943486031943521/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree018.table
  base := (-1672817371091365440230006338884958495221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-749205624423346981955172729314028500000000000)
      constant := (3440622494685019961570144761996163346720251499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree018.table
  base := (-67416833206884493093446974316511616887/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-9750421715666956555313166937231808000000000000)
      constant := (44821811285727966887204601195114775345396659725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1287399646787699647/625000000000000000)
  centralHi := (205983943486031943521/100000000000000000000)
  directionLo := (2119557292195738673/1000000000000000000)
  directionHi := (211955729219573867301/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree019.table
  base := (-646605664594545913545507105737156179093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (160446)
      previous := (80223)
      next := (80223)
      square := (1438175005728886975547853314030000000000000)
      linear := (-28474847495081344159531533463194250000000000)
      constant := (136876232108393781043649464392362368008646844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree019.table
  base := (-2597636523437770338662595809451561218841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (160446)
      previous := (80223)
      next := (80223)
      square := (1438175005728886975547853314030000000000000)
      linear := (-28506276144682062843437736551350500000000000)
      constant := (137169896914344318054143837782895787952763107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2119557292195738673/1000000000000000000)
  centralHi := (211955729219573867301/100000000000000000000)
  directionLo := (217763810868440298361/100000000000000000000)
  directionHi := (108881905434220149181/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree020.table
  base := (-1692151665576411898919061027898232635111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-10819166773945219717764521679343878000000000000)
      constant := (54442825280810317202953784602950760431908626634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree020.table
  base := (-212141134724781116174801571848286650977/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-10831109660793492817648878852843253000000000000)
      constant := (54561679422395916652980734520758568086124121904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217763810868440298361/100000000000000000000)
  centralHi := (108881905434220149181/50000000000000000000)
  directionLo := (223420955818585546461/100000000000000000000)
  directionHi := (111710477909292773231/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree021.table
  base := (-2039838929322793635539734601485607194611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-11358913602166074193938159778474631750000000000)
      constant := (59812102752537911898174136955194621987624619634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree021.table
  base := (-4088495558753458354002169762405760945281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-11371453633356760948816734810648975500000000000)
      constant := (59944349951890407003701010550514028023689348307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223420955818585546461/100000000000000000000)
  centralHi := (111710477909292773231/50000000000000000000)
  directionLo := (4578767068713361509/2000000000000000000)
  directionHi := (228938353435668075451/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree022.table
  base := (-4683620223846684016178360851596019271691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-98336036614768005538114032046325500000000000)
      constant := (541436891007024788066688978912921975307954137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree022.table
  base := (-1172853596576318436448545636803545025241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-98444608313388670082517279078138000000000000)
      constant := (542645129835401139848829605523855477786175948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4578767068713361509/2000000000000000000)
  centralHi := (228938353435668075451/100000000000000000000)
  directionLo := (58581468832291256309/25000000000000000000)
  directionHi := (234325875329165025237/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree023.table
  base := (-2602717706240201763777177408652391796747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-12438407258607783146285435976736139250000000000)
      constant := (71542824594688084614364843918476412401771151618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree023.table
  base := (-52123113564754191188694730541925669869/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-12452141578483297211152446726260420500000000000)
      constant := (71703532527641954409732625851469298352537874300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58581468832291256309/25000000000000000000)
  centralHi := (234325875329165025237/100000000000000000000)
  directionLo := (119796141448424694203/50000000000000000000)
  directionHi := (239592282896849388407/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree024.table
  base := (-2826478032026649573215814990185881103911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-12978154086828637622459074075866893000000000000)
      constant := (77894537313210452838586395715532805715001653834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree024.table
  base := (-1414752722380537596904907906203200944117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-12992485551046565342320302684066143000000000000)
      constant := (78070322284048745072018733549586551937121316796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119796141448424694203/50000000000000000000)
  centralHi := (239592282896849388407/100000000000000000000)
  directionLo := (244745394642408799093/100000000000000000000)
  directionHi := (122372697321204399547/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree025.table
  base := (-754097824449876326608231890543390201117/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-13517900915049492098632712174997646750000000000)
      constant := (84565253900803300601424190153887426257688365592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree025.table
  base := (-6038105310192550522278380118054131430793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-13532829523609833473488158641871865500000000000)
      constant := (84756686507919304602670575703951334648379902571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244745394642408799093/100000000000000000000)
  centralHi := (122372697321204399547/50000000000000000000)
  directionLo := (124896111202083613389/50000000000000000000)
  directionHi := (249792222404167226779/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree026.table
  base := (-1587620170805326909682349435435569070559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-1081357518713103582677411559548338500000000000)
      constant := (7042447220891851843129412902755014598465649284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree026.table
  base := (-3177576215725847453114786997298818204899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-1082551807397930892665847276898276000000000000)
      constant := (7058420706037536619231344603049962268983613562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124896111202083613389/50000000000000000000)
  centralHi := (249792222404167226779/100000000000000000000)
  directionLo := (254739083276511500391/100000000000000000000)
  directionHi := (31842385409563937549/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree027.table
  base := (-3305372658759208997125440353589758362807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-14597394571491201050979988373259154250000000000)
      constant := (98851551161086597482353294276093204755997413258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree027.table
  base := (-206713740748137462027375796319844376359/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-1124116728364336133524913119806408500000000000)
      constant := (7621231424065078504190901755745605808230400672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254739083276511500391/100000000000000000000)
  centralHi := (31842385409563937549/12500000000000000000)
  directionLo := (129795846161868734619/50000000000000000000)
  directionHi := (259591692323737469239/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree028.table
  base := (-3408768972226491088716020706669389870709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-15137141399712055527153626472389908000000000000)
      constant := (106462216250306647871725189191075991032496564446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree028.table
  base := (-1364224286100699271239858803069348523259/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-15153861441299637866991726515289033000000000000)
      constant := (106704059048260090482266882189590185165109035365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129795846161868734619/50000000000000000000)
  centralHi := (259591692323737469239/100000000000000000000)
  directionLo := (33044404995978161963/12500000000000000000)
  directionHi := (52871047993565059141/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree029.table
  base := (-3487100773152429070994793713015512163139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-15676888227932910003327264571520661750000000000)
      constant := (114381910816737660950206158939395098110437558866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree029.table
  base := (-872166737225101900820880752100893883297/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-15694205413862905998159582473094755500000000000)
      constant := (114641726264341542758961319453112971939255189272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33044404995978161963/12500000000000000000)
  centralHi := (52871047993565059141/20000000000000000000)
  directionLo := (53806891407473453627/20000000000000000000)
  directionHi := (33629307129670908517/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree030.table
  base := (-7083557435590599307996857861654086369969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-16216635056153764479500902670651415500000000000)
      constant := (122609032769603174308547297683786665686303993443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree030.table
  base := (-7086292199638372394222855243757543642171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-16234549386426174129327438430900478000000000000)
      constant := (122887411601627349179990246526547278195162271137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53806891407473453627/20000000000000000000)
  centralHi := (33629307129670908517/12500000000000000000)
  directionLo := (13681683490010972707/5000000000000000000)
  directionHi := (273633669800219454141/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree031.table
  base := (-7147986782122584154049596140490664253517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-1288952452644201458128810828444782250000000000)
      constant := (10087863842652439953118659748908684818179623923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree031.table
  base := (-7150371775629538193165904862685161974657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-16774893358989442260495294388706200500000000000)
      constant := (131439766159606738595152405251253824310955098579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13681683490010972707/5000000000000000000)
  centralHi := (273633669800219454141/100000000000000000000)
  directionLo := (278156846802806653223/100000000000000000000)
  directionHi := (34769605850350831653/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree032.table
  base := (-7169499339215430272349701560307287181841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-17296128712595473431848178868912923000000000000)
      constant := (139980361126924330652607370973539192051930042627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree032.table
  base := (-7171577134981367894408919708344327809113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-17315237331552710391663150346511923000000000000)
      constant := (140297651671712957036280346791642864420611755611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278156846802806653223/100000000000000000000)
  centralHi := (34769605850350831653/12500000000000000000)
  directionLo := (282607638959431823067/100000000000000000000)
  directionHi := (70651909739857955767/25000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree033.table
  base := (-3574895704191933927705650961496121091459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-147403930089391139735717495603666750000000000)
      constant := (1232417049892784826534974837870081524623065826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree033.table
  base := (-893949976034836290822624456969700448741/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-147566787637322136552322366151385500000000000)
      constant := (1235207500803543947921905398080952160102467896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282607638959431823067/100000000000000000000)
  centralHi := (70651909739857955767/25000000000000000000)
  directionLo := (286989414043739748069/100000000000000000000)
  directionHi := (28698941404373974807/10000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree034.table
  base := (-443143421408947561904512900837383127737/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-18375622369037182384195455067174430500000000000)
      constant := (158567722659601428007186078302988816003992581424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree034.table
  base := (-3545933615154427343771827802084524104857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-18395925276679246653998862262123368000000000000)
      constant := (158926323363028019977909765016806428591969275958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286989414043739748069/100000000000000000000)
  centralHi := (28698941404373974807/10000000000000000000)
  directionLo := (291305286509039521539/100000000000000000000)
  directionHi := (14565264325451976077/5000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree035.table
  base := (-6992217811832379437639981484953320796087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-18915369197258036860369093166305184250000000000)
      constant := (168315453761253841461483377802387386418167108789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree035.table
  base := (-6993583980529619706233196702678295497909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-18936269249242514785166718219929090500000000000)
      constant := (168695614945051737206855319193668841710375880623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291305286509039521539/100000000000000000000)
  centralHi := (14565264325451976077/5000000000000000000)
  directionLo := (295558143388163339591/100000000000000000000)
  directionHi := (36944767923520417449/12500000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree036.table
  base := (-3428290314320415452127626833635824010507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-19455116025478891336542731265435938000000000000)
      constant := (178365077124888898824087357083754771481323137058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree036.table
  base := (-6857766579725080002697653139031594784711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-19476613221805782916334574177734813000000000000)
      constant := (178767405108923158903109079340768179806717504517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295558143388163339591/100000000000000000000)
  centralHi := (36944767923520417449/12500000000000000000)
  directionLo := (149875333442500336067/50000000000000000000)
  directionHi := (59950133377000134427/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree037.table
  base := (-6684244139057684495821384307375568412101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-19994862853699745812716369364566691750000000000)
      constant := (188716103859687027150930615896100228092670710847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree037.table
  base := (-3342636425791271285914855336481705647351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-20016957194369051047502430135540535500000000000)
      constant := (189141206736887976727700249171381947599819585194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149875333442500336067/50000000000000000000)
  centralHi := (59950133377000134427/20000000000000000000)
  directionLo := (75971338539999394089/25000000000000000000)
  directionHi := (303885354159997576357/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree038.table
  base := (-6475935029498632476587999100973116418323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (160446)
      previous := (80223)
      next := (80223)
      square := (1438175005728886975547853314030000000000000)
      linear := (-56882575296178948168670380785865500000000000)
      constant := (552266264029326915076682026424484381623977921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree038.table
  base := (-6476826699079704544471595615238867922323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (160446)
      previous := (80223)
      next := (80223)
      square := (1438175005728886975547853314030000000000000)
      linear := (-56945432595380385536482786962178000000000000)
      constant := (553508611519303591223791351657238885758185921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75971338539999394089/25000000000000000000)
  centralHi := (303885354159997576357/100000000000000000000)
  directionLo := (307964534724197867373/100000000000000000000)
  directionHi := (153982267362098933687/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree039.table
  base := (-779033333024945797737786748677249594909/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-1621104346933958058851049658679092250000000000)
      constant := (16178521629912878667947740981252703631995739768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree039.table
  base := (-3116519506100573959610806118004972713703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-1622895779961199023833703234703998500000000000)
      constant := (16214866482919584859517255599745649042535478514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307964534724197867373/100000000000000000000)
  centralHi := (153982267362098933687/50000000000000000000)
  directionLo := (62398077157180474053/20000000000000000000)
  directionHi := (155995192892951185133/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree040.table
  base := (-5953756757303207449119135936785700102713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-21614103338362309241237283661958953000000000000)
      constant := (221573789496999159490050206277087924839574114811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree040.table
  base := (-1488606327823833256716183972742403612269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-1664460700927604264692769077612131000000000000)
      constant := (17082375427351504823791534085078171271249911244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62398077157180474053/20000000000000000000)
  centralHi := (155995192892951185133/50000000000000000000)
  directionLo := (78991236459250935969/25000000000000000000)
  directionHi := (315964945837003743877/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree041.table
  base := (-5640842288937393890893315218247505013689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-22153850166583163717410921761089706750000000000)
      constant := (233126898098505693450300271479520358590149160283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree041.table
  base := (-2820710317932655153736862693738719384059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-22178333084622123572173853966763425500000000000)
      constant := (233649210552826549336938902569196054306957889346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78991236459250935969/25000000000000000000)
  centralHi := (315964945837003743877/100000000000000000000)
  directionLo := (319890126719667962989/100000000000000000000)
  directionHi := (31989012671966796299/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree042.table
  base := (-21175568380622295732529762683792164841/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-22693596994804018193584559860220460500000000000)
      constant := (244979897548727565828644514962583359048385906750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree042.table
  base := (-5294392108911267449673252030960303824609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-22718677057185391703341709924569148000000000000)
      constant := (245528045797828537477122615711432347717284305523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319890126719667962989/100000000000000000000)
  centralHi := (31989012671966796299/10000000000000000000)
  directionLo := (16188386218804342649/5000000000000000000)
  directionHi := (323767724376086852981/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree043.table
  base := (-4913217494528955992530233188163377175519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-23233343823024872669758197959351214250000000000)
      constant := (257132611064480160212038157235867430897937509293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree043.table
  base := (-2456824769875222860930957692992708910043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-23259021029748659834509565882374870500000000000)
      constant := (257707210364425303723857132574186923878360704642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16188386218804342649/5000000000000000000)
  centralHi := (323767724376086852981/100000000000000000000)
  directionLo := (163799714226409948513/50000000000000000000)
  directionHi := (327599428452819897027/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree044.table
  base := (-224954062879116317653972358763269933563/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (36822)
      previous := (18411)
      next := (18411)
      square := (330057963806820214985870976710000000000000)
      linear := (-15113217197231867225640073781616000000000000)
      constant := (171382637908920956856171049416413816079675140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree044.table
  base := (-1124863592889844929984311407951156787063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-196688966961255603022127453224633000000000000)
      constant := (2232946742077063829564117792996537884793253364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163799714226409948513/50000000000000000000)
  centralHi := (327599428452819897027/100000000000000000000)
  directionLo := (82846707726363054179/25000000000000000000)
  directionHi := (331386830905452216717/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree045.table
  base := (-810341035501118905787942621467635162807/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-24312837479466581622105474157612721750000000000)
      constant := (282336606701556810909457136806869949966660283145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree045.table
  base := (-162081089282509528798422365668189975869/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-24339708974875196096845277797986315500000000000)
      constant := (282965956794411460098833230160094789034571518575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82846707726363054179/25000000000000000000)
  centralHi := (331386830905452216717/100000000000000000000)
  directionLo := (335131433727878319691/100000000000000000000)
  directionHi := (83782858431969579923/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree046.table
  base := (-1785638230133401774704264192587830225249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-24852584307687436098279112256743475500000000000)
      constant := (295387656571482026397822713668887434779953359206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree046.table
  base := (-1785777152721770332295070094380274121681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-24880052947438464228013133755792038000000000000)
      constant := (296045307648438633749010229497409715023362158214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335131433727878319691/100000000000000000000)
  centralHi := (83782858431969579923/25000000000000000000)
  directionLo := (67766931182531149327/20000000000000000000)
  directionHi := (84708663978163936659/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree047.table
  base := (-1528976559117208476394854399416346899209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-25392331135908290574452750355874229250000000000)
      constant := (308737949312710842474237354610241375383174443446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree047.table
  base := (-3058192709502021931742838518336703594051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-25420396920001732359180989713597760500000000000)
      constant := (309424519133592027551659534086071292447757357497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67766931182531149327/20000000000000000000)
  centralHi := (84708663978163936659/25000000000000000000)
  directionLo := (42812229966738245267/12500000000000000000)
  directionHi := (342497839733905962137/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree048.table
  base := (-2511868522705077352765200110228821276781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-25932077964129145050626388455004983000000000000)
      constant := (322387409189952346740593925684188472151516078807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree048.table
  base := (-1256037516679831619193167528258077071749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-25960740892565000490348845671403483000000000000)
      constant := (323103515958741241033282395409160546321152230206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42812229966738245267/12500000000000000000)
  centralHi := (342497839733905962137/100000000000000000000)
  directionLo := (43265282053956244873/12500000000000000000)
  directionHi := (69224451286329991797/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree049.table
  base := (-241641905812438441882690531834263096987/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-26471824792349999526800026554135736750000000000)
      constant := (336335972278392573300849264230197100510380628712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree049.table
  base := (-1933313166760161495887852876627343622327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-26501084865128268621516701629209205500000000000)
      constant := (337082234586959646671668201742818699885780746069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43265282053956244873/12500000000000000000)
  centralHi := (69224451286329991797/20000000000000000000)
  directionLo := (349709111365834117489/100000000000000000000)
  directionHi := (34970911136583411749/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree050.table
  base := (-330462076833774642190553028404392378277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-27011571620570854002973664653266490500000000000)
      constant := (350583584621935648484251079986643787143023082876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree050.table
  base := (-1322001531559681063332683606795971493353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-27041428837691536752684557587014928000000000000)
      constant := (351360621400512955967017292980139690324585018891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349709111365834117489/100000000000000000000)
  centralHi := (34970911136583411749/10000000000000000000)
  directionLo := (176629774349644889417/50000000000000000000)
  directionHi := (70651909739857955767/20000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree051.table
  base := (-678087905419445900438728711953193968851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-27551318448791708479147302752397244250000000000)
      constant := (365130200678653088593677426824747411687393553097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree051.table
  base := (-339109904366748099625757919444732266133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-27581772810254804883852413544820650500000000000)
      constant := (365938631152320316505800242012165823740709155102) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176629774349644889417/50000000000000000000)
  centralHi := (70651909739857955767/20000000000000000000)
  directionLo := (178387327830601804641/50000000000000000000)
  directionHi := (356774655661203609283/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree052.table
  base := (-30027095892642784423421916595818267/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-2160851175154812535024687757809846000000000000)
      constant := (29228906308357952303455620541452520520985867072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree052.table
  base := (-1017619828169375945054029126321068987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-2163239752524467155001559192509721000000000000)
      constant := (29293555819935797129522703857362968338771157706) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178387327830601804641/50000000000000000000)
  centralHi := (356774655661203609283/100000000000000000000)
  directionLo := (360255466436131850609/100000000000000000000)
  directionHi := (36025546643613185061/10000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree053.table
  base := (706593069597508346649802782911709698101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-28630812105233417431494578950658751750000000000)
      constant := (395120296166568301911568092412158521579383247153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree053.table
  base := (706495431881429259366672619772937345781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-2204804673490872395860625035417853500000000000)
      constant := (30461028669147423542862174033442302644951059861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360255466436131850609/100000000000000000000)
  centralHi := (36025546643613185061/10000000000000000000)
  directionLo := (45462870714748411621/12500000000000000000)
  directionHi := (363702965717987292969/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree054.table
  base := (723704139565163868843451023104939915227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-29170558933454271907668217049789505500000000000)
      constant := (410563715766747621804284532234559463235112795262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree054.table
  base := (1447324320835414933576551947422908505127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-29202804727944609277355981418237818000000000000)
      constant := (411470045079907632984060805620844123488361882331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45462870714748411621/12500000000000000000)
  centralHi := (363702965717987292969/100000000000000000000)
  directionLo := (367118091963613198639/100000000000000000000)
  directionHi := (4588976149545164983/1250000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree055.table
  base := (1110241594285720343147671044910351634389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-245539717038637408130924422718349250000000000)
      constant := (3523190228877930982269814297453638677627875154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree055.table
  base := (555102754479017456292286393731731860729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-245811146285189069491932540297880500000000000)
      constant := (3530960494674400376123060332560586914239604788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367118091963613198639/100000000000000000000)
  centralHi := (4588976149545164983/1250000000000000000)
  directionLo := (370501740376409670057/100000000000000000000)
  directionHi := (185250870188204835029/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree056.table
  base := (75644585999519648749407916912985369269/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-30250052589895980860015493248051013000000000000)
      constant := (442347182438755045465920411065924177235820378280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree056.table
  base := (3025721422503324913027765058663898457019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-30283492673071145539691693333849263000000000000)
      constant := (443321877661861535583848571408935043730513610207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370501740376409670057/100000000000000000000)
  centralHi := (185250870188204835029/50000000000000000000)
  directionLo := (93463691411723151997/25000000000000000000)
  directionHi := (373854765646892607989/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree057.table
  base := (3863280033445445705089494056760123578329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (12342)
      previous := (6171)
      next := (6171)
      square := (110628846594529767349834870310000000000000)
      linear := (-6560792545944350167523786777579750000000000)
      constant := (97738588010363575860472095067480560890477809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree057.table
  base := (386322675776091995925453333298391464617/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (160446)
      previous := (80223)
      next := (80223)
      square := (1438175005728886975547853314030000000000000)
      linear := (-85384589046078708229527837373005500000000000)
      constant := (1273398897943690034122062592639323291488425410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93463691411723151997/25000000000000000000)
  centralHi := (373854765646892607989/100000000000000000000)
  directionLo := (377177984473958276963/100000000000000000000)
  directionHi := (94294496118489569241/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree058.table
  base := (4732948491528158258284888521801291320867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-31329546246337689812362769446312520500000000000)
      constant := (475326037076287115632119053814510556274178288551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree058.table
  base := (946580547901273707530963837233145138189/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-31364180618197681802027405249460708000000000000)
      constant := (476371579553188268248964473923943462955780191085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377177984473958276963/100000000000000000000)
  centralHi := (94294496118489569241/25000000000000000000)
  directionLo := (1521888711551706221/400000000000000000)
  directionHi := (380472177887926555251/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree059.table
  base := (563476815401403484990354324353757179047/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-31869293074558544288536407545443274250000000000)
      constant := (492263701337742602595852328442686924121121260910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree059.table
  base := (5634728874833031146648356646994897809501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-31904524590760949933195261207266430500000000000)
      constant := (493345598211451519415657346579826278049568571353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1521888711551706221/400000000000000000)
  centralHi := (380472177887926555251/100000000000000000000)
  directionLo := (383738093394083755133/100000000000000000000)
  directionHi := (191869046697041877567/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree060.table
  base := (1642180395659119893828828169067444755197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-32409039902779398764710045644574028000000000000)
      constant := (509500176414630721120163423997653455951291528164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree060.table
  base := (3284343935114034458831934474655028267593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-32444868563324218064363117165072153000000000000)
      constant := (510619048312288709728108408684949118533674975658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383738093394083755133/100000000000000000000)
  centralHi := (191869046697041877567/50000000000000000000)
  directionLo := (386976446953391550009/100000000000000000000)
  directionHi := (38697644695339155001/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree061.table
  base := (3767397029315949105554420104562798100659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-32948786731000253240883683743704781750000000000)
      constant := (527035453948857407934505531393856474046894530254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree061.table
  base := (7534765132092342901662474521288074165071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-32985212535887486195530973122877875500000000000)
      constant := (528191921568680787336689084222107505872608062563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386976446953391550009/100000000000000000000)
  centralHi := (38697644695339155001/10000000000000000000)
  directionLo := (39018792481523000353/10000000000000000000)
  directionHi := (390187924815230003531/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree062.table
  base := (341318926345890120711261287553456772299/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-33488533559221107717057321842835535500000000000)
      constant := (544869526885784370499388884317506441806757601175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree062.table
  base := (266654635788654277572451230972133046113/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-33525556508450754326698829080683598000000000000)
      constant := (546064210987410780601210156178201143957300972448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39018792481523000353/10000000000000000000)
  centralHi := (390187924815230003531/100000000000000000000)
  directionLo := (49171648151933056373/12500000000000000000)
  directionHi := (78674637043092890197/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree063.table
  base := (4781624198390964839147729726026387166461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-34028280387441962193230959941966289250000000000)
      constant := (563002389270961487273040543579407870367960256466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree063.table
  base := (9563227117182985587710998935260738789537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-34065900481014022457866685038489320500000000000)
      constant := (564235910667078388440415602599476083897604954061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49171648151933056373/12500000000000000000)
  centralHi := (78674637043092890197/20000000000000000000)
  directionLo := (99133214987934485889/25000000000000000000)
  directionHi := (396532859951737943557/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree064.table
  base := (10625610922450766864129746962727219048579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-34568027215662816669404598041097043000000000000)
      constant := (581434036078557422639575944727716111518392730887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree064.table
  base := (10625592677991923703501135259678544827059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-34606244453577290589034540996295043000000000000)
      constant := (582707015627647686724862069157732712715679934327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99133214987934485889/25000000000000000000)
  centralHi := (396532859951737943557/100000000000000000000)
  directionLo := (79933511169333512569/20000000000000000000)
  directionHi := (199833777923333781423/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree065.table
  base := (5860026632681676940553814733664859139897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-2700598003375667011198325856940599750000000000)
      constant := (46166497158965027385774979160224490322617181714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree065.table
  base := (11720037626957019413382090470116255440351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-2703583725087735286169415150315443500000000000)
      constant := (46267501666661935051728024189419237372639972031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79933511169333512569/20000000000000000000)
  centralHi := (199833777923333781423/50000000000000000000)
  directionLo := (100694464027135589637/25000000000000000000)
  directionHi := (402777856108542358549/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree066.table
  base := (12846569120272162336381561396472250835711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-294607610513260542328527886275690500000000000)
      constant := (5117303030202244319496473052485958366921991723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree066.table
  base := (12846555718840436129049759183409447744993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (36822)
      previous := (18411)
      next := (18411)
      square := (330057963806820214985870976710000000000000)
      linear := (-22687178893009425843210586720856000000000000)
      constant := (394499316743530676454573482110287435635942473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100694464027135589637/25000000000000000000)
  centralHi := (402777856108542358549/100000000000000000000)
  directionLo := (405864321598164342357/100000000000000000000)
  directionHi := (202932160799082171179/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree067.table
  base := (112041225322302825119144947123190042729/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-36187267700325380097925512338489304250000000000)
      constant := (638521643820285215701264529083403317408911354625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree067.table
  base := (14005141683482163726742321087388614355917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-36227276371267094982538108869712210500000000000)
      constant := (639916723347877309667792866899102472671600536201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405864321598164342357/100000000000000000000)
  centralHi := (202932160799082171179/50000000000000000000)
  directionLo := (408927492009625941717/100000000000000000000)
  directionHi := (204463746004812970859/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree068.table
  base := (15195800908527200981463671504153240996909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-36727014528546234574099150437620058000000000000)
      constant := (658148392013256949999587733298445344984817766377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree068.table
  base := (3039158214714192037256544850831155504519/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-36767620343830363113705964827517933000000000000)
      constant := (659585413472096791771827053612898444733538138535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408927492009625941717/100000000000000000000)
  centralHi := (204463746004812970859/50000000000000000000)
  directionLo := (1287399646787699647/312500000000000000)
  directionHi := (411967886972063887041/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree069.table
  base := (16418508558675367554600071917722070811541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-37266761356767089050272788536750811750000000000)
      constant := (678073909080477260677185797959035841318733491473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree069.table
  base := (16418500136180780931557171361188901617949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-37307964316393631244873820785323655500000000000)
      constant := (679553493479121887184466699349883946944207193497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1287399646787699647/312500000000000000)
  centralHi := (411967886972063887041/100000000000000000000)
  directionLo := (414986007078758890391/100000000000000000000)
  directionHi := (51873250884844861299/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree070.table
  base := (220915911446665626182751901493548454191/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-2908192937306764886649725125837043500000000000)
      constant := (53715245631139773633217358476707544420951365680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree070.table
  base := (17673265704362535872593630057211732216183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-37848308288956899376041676743129378000000000000)
      constant := (699820961570591054250850915623289704399156165099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414986007078758890391/100000000000000000000)
  centralHi := (51873250884844861299/12500000000000000000)
  directionLo := (417982334849352505051/100000000000000000000)
  directionHi := (104495583712338126263/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree071.table
  base := (18960091278802183708389532722245550869523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-38346255013208798002620064735012319250000000000)
      constant := (718821242852562930107946283274776286227598744119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree071.table
  base := (18960085105660225579776284639174954021243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-38388652261520167507209532700935100500000000000)
      constant := (720387816228942136326874072638692054259574901279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417982334849352505051/100000000000000000000)
  centralHi := (104495583712338126263/25000000000000000000)
  directionLo := (420957335630418441291/100000000000000000000)
  directionHi := (105239333907604610323/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree072.table
  base := (10139480684124569713901621679688190481239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-38886001841429652478793702834143073000000000000)
      constant := (739643056729218424906922355454168117058686019734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree072.table
  base := (20278956084909296045511098816837865760011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-38928996234083435638377388658740823000000000000)
      constant := (741254056173573175925661874106568943585419526383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420957335630418441291/100000000000000000000)
  centralHi := (105239333907604610323/25000000000000000000)
  directionLo := (2119557292195738673/500000000000000000)
  directionHi := (423911458439147734601/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree073.table
  base := (21629881260009877056361050871480429309991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-39425748669650506954967340933273826750000000000)
      constant := (760763633742197890640450629835111108779653819323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree073.table
  base := (10814938369543766256594876810582561079351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-39469340206646703769545244616546545500000000000)
      constant := (762419680323847299331030016275396744456935406806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2119557292195738673/500000000000000000)
  centralHi := (423911458439147734601/100000000000000000000)
  directionLo := (426845136754478901061/100000000000000000000)
  directionHi := (213422568377239450531/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree074.table
  base := (23012849330137219483930208864865884636831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-39965495497871361431140979032404580500000000000)
      constant := (782182972969338050945010895979708185282428393843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree074.table
  base := (4602569092467379901820222674694605495649/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-40009684179209971900713100574352268000000000000)
      constant := (783884687767873203525125209616627884197603857985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426845136754478901061/100000000000000000000)
  centralHi := (213422568377239450531/50000000000000000000)
  directionLo := (42975878925961981141/10000000000000000000)
  directionHi := (429758789259619811411/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree075.table
  base := (24427864207996788560436290644639923567339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-40505242326092215907314617131535334250000000000)
      constant := (803901073632320062284948940465984372134671653167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree075.table
  base := (30534826124460599247784927643204198711/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-40550028151773240031880956532157990500000000000)
      constant := (805649077736159581362150011639123774424259986400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42975878925961981141/10000000000000000000)
  centralHi := (429758789259619811411/100000000000000000000)
  directionLo := (43265282053956244873/10000000000000000000)
  directionHi := (432652820539562448731/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree076.table
  base := (5174984947352337203666799223281895569261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (160446)
      previous := (80223)
      next := (80223)
      square := (1438175005728886975547853314030000000000000)
      linear := (-113698030898374156186948075431208000000000000)
      constant := (2287861315995114404427546709139718233652237765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree076.table
  base := (5174984381462109799098165065128986862211/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (160446)
      previous := (80223)
      next := (80223)
      square := (1438175005728886975547853314030000000000000)
      linear := (-113823745496777030922572887783833000000000000)
      constant := (2292833378336239846028497289667992481671289515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43265282053956244873/10000000000000000000)
  centralHi := (432652820539562448731/100000000000000000000)
  directionLo := (435527621736880596723/100000000000000000000)
  directionHi := (108881905434220149181/25000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree077.table
  base := (27354029940067894332740251648713585563823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-343675503987883676526131349833031750000000000)
      constant := (7010194683807070476377187872472924911738521339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree077.table
  base := (2735402752066902209960103995322040172053/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-344055504933056002431542714444375500000000000)
      constant := (7025421510327472819470060612872684189024447290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435527621736880596723/100000000000000000000)
  centralHi := (108881905434220149181/25000000000000000000)
  directionLo := (438383571168819995259/100000000000000000000)
  directionHi := (21919178558440999763/5000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree078.table
  base := (3608147374233708808716796733030356469519/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-3240344831596521487371963956071353500000000000)
      constant := (66988302935664684453522622335191230476310475512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree078.table
  base := (902036778920188023059683830119402103619/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-3243927697651003417337271108121166000000000000)
      constant := (67133733598810750131469612708512820430221809248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438383571168819995259/100000000000000000000)
  centralHi := (21919178558440999763/5000000000000000000)
  directionLo := (55152629363554653581/12500000000000000000)
  directionHi := (441221034908437228649/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree079.table
  base := (7602092800671006015125201390614988709029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-42664229638975633812009169528058349250000000000)
      constant := (893761078948260308230904414761227808288240478948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree079.table
  base := (7602092358652819429658404815412059238861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-3285492618617408658196336951029298500000000000)
      constant := (68900034714922847274965418929648483607200749364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55152629363554653581/12500000000000000000)
  centralHi := (441221034908437228649/100000000000000000000)
  directionLo := (444040367332314620563/100000000000000000000)
  directionHi := (111010091833078655141/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree080.table
  base := (999487686860619595273571832882108962527/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-43203976467196488288182807627189103000000000000)
      constant := (916972978761200442666824958796152700062331024992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree080.table
  base := (3997950558555862520496032503315947556423/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-43251748014589580687720236321186603000000000000)
      constant := (918961745948801448313638147636959256142059758552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444040367332314620563/100000000000000000000)
  centralHi := (111010091833078655141/25000000000000000000)
  directionLo := (223420955818585546461/50000000000000000000)
  directionHi := (446841911637171092923/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree081.table
  base := (839772070726345939517428111027748499533/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-43743723295417342764356445726319856750000000000)
      constant := (940483637321156441167151120831075091177900005960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree081.table
  base := (16795440768895944380935204858142762502111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-43792091987152848818888092278992325500000000000)
      constant := (942522420471181514255438291803584997073972475366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223420955818585546461/50000000000000000000)
  centralHi := (446841911637171092923/100000000000000000000)
  directionLo := (449626000327501008201/100000000000000000000)
  directionHi := (224813000163750504101/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree082.table
  base := (550471895830406437314594788601456360241/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-44283470123638197240530083825450610500000000000)
      constant := (964293054390720296694767242614321584949793684672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree082.table
  base := (17615100114951307217873244531991179571727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-44332435959716116950055948236798048000000000000)
      constant := (966382474626759504397919984817837993711687784262) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449626000327501008201/100000000000000000000)
  centralHi := (224813000163750504101/50000000000000000000)
  directionLo := (113098238919050606959/25000000000000000000)
  directionHi := (452392955676202427837/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree083.table
  base := (7380312227796504151807211733502859127369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-3447939765527619362823363224967797250000000000)
      constant := (76030863828425712358444544837632208658650526445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree083.table
  base := (18450780098260390289511867396964797873699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-44872779932279385081223804194603770500000000000)
      constant := (990541908217775900238151063335328711577697196494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113098238919050606959/25000000000000000000)
  centralHi := (452392955676202427837/100000000000000000000)
  directionLo := (455143090160001190157/100000000000000000000)
  directionHi := (227571545080000595079/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree084.table
  base := (38604961948799068234857334170033596177243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-45362963780079906192877360023712118000000000000)
      constant := (1012808163288511984479594452305799910315035969279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree084.table
  base := (38604961143804266876437728255860087920513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-45413123904842653212391660152409493000000000000)
      constant := (1015000721077371572228747681432247000505927068589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455143090160001190157/100000000000000000000)
  centralHi := (227571545080000595079/50000000000000000000)
  directionLo := (457876706871336150901/100000000000000000000)
  directionHi := (228938353435668075451/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree085.table
  base := (40340403511311290615301825305632035753097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-45902710608300760669050998122842871750000000000)
      constant := (1037513854804960888317123827948078990390690890741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree085.table
  base := (2521275176489376333990897229612693442331/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-45953467877405921343559516110215215500000000000)
      constant := (1039758913064762671531363330198566547542677765488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457876706871336150901/100000000000000000000)
  centralHi := (228938353435668075451/50000000000000000000)
  directionLo := (92118819981648485657/20000000000000000000)
  directionHi := (230297049954121214143/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree086.table
  base := (42107885614464733516638019950809207134673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-46442457436521615145224636221973625500000000000)
      constant := (1062518304198465214087202119462189876042795467069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree086.table
  base := (42107885027423574416392927078615510139189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-46493811849969189474727372068020938000000000000)
      constant := (1064816484061168848080171815193239531904068891217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92118819981648485657/20000000000000000000)
  centralHi := (230297049954121214143/50000000000000000000)
  directionLo := (57911944342956537533/12500000000000000000)
  directionHi := (92659110948730460053/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree087.table
  base := (43907408079315506247903059008812068624841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-46982204264742469621398274321104379250000000000)
      constant := (1087821511367411136629293994421464062284509336373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree087.table
  base := (43907407578108063974146267482473433712619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-47034155822532457605895228025826660500000000000)
      constant := (1090173433966377186289797487377905188847761837007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57911944342956537533/12500000000000000000)
  centralHi := (92659110948730460053/20000000000000000000)
  directionLo := (232990674287713199857/50000000000000000000)
  directionHi := (93196269715085279943/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree088.table
  base := (4573897075486528712652916727497128691549/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-392743397462506810723734813390373000000000000)
      constant := (9201846910959122363479242098947144249494394570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree088.table
  base := (45738970326997993680429834329607472195249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-393177684256989468901347801517623000000000000)
      constant := (9221733575998699259578223299244976867012303557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232990674287713199857/50000000000000000000)
  centralHi := (93196269715085279943/20000000000000000000)
  directionLo := (58581468832291256309/12500000000000000000)
  directionHi := (468651750658330050473/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree089.table
  base := (9520514702740370226324059553607614542631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-48061697921184178573745550519365886750000000000)
      constant := (1139324198702041807927494135149167983009070706215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree089.table
  base := (59503216435612790915926693476554183409/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-48114843767658993868230939941438105500000000000)
      constant := (1141785470178241005802081087547134077512830701600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58581468832291256309/12500000000000000000)
  centralHi := (468651750658330050473/100000000000000000000)
  directionLo := (94261404523816019497/20000000000000000000)
  directionHi := (235653511309540048743/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree090.table
  base := (49498216248319500205512247276599557709259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-48601444749405033049919188618496640500000000000)
      constant := (1165523678734327709309672727164944217237625850927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree090.table
  base := (49498215936627791122911437021063499533133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-48655187740222261999398795899243828000000000000)
      constant := (1168040556353404377822036678742309444525388173449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94261404523816019497/20000000000000000000)
  centralHi := (235653511309540048743/50000000000000000000)
  directionLo := (94789483751101123163/20000000000000000000)
  directionHi := (59243427344438201977/12500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree091.table
  base := (25712949434006683119294041768927042725213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-3780091659817375963545602055202107250000000000)
      constant := (91693993559338806050528751244900342142497558106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree091.table
  base := (12856474650507833944587302957253562082279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-3784271670214271548505127065926888500000000000)
      constant := (91891924705429108003504757687304089100014115996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94789483751101123163/20000000000000000000)
  centralHi := (59243427344438201977/12500000000000000000)
  directionLo := (476573186320790727413/100000000000000000000)
  directionHi := (238286593160395363707/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree092.table
  base := (53385621296258091609912671387343426561651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-49680938405846742002266464816758148000000000000)
      constant := (1218818911269816962067976372896905575928313205303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree092.table
  base := (26692810534654905350646846240472644555831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-3825836591180676789364192908835021000000000000)
      constant := (93957604968227080550089233194676638173686507822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476573186320790727413/100000000000000000000)
  centralHi := (238286593160395363707/50000000000000000000)
  directionLo := (119796141448424694203/25000000000000000000)
  directionHi := (479184565793698776813/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree093.table
  base := (55377383468495348494361533257397863730887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-50220685234067596478440102915888901750000000000)
      constant := (1245914663692905519412500137344313649480362875611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree093.table
  base := (55377383274875362017862600630948387894527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-50276219657912066392902363772660995500000000000)
      constant := (1248602086566416753552985550124279830004820840531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119796141448424694203/25000000000000000000)
  centralHi := (479184565793698776813/100000000000000000000)
  directionLo := (96356358227122749553/20000000000000000000)
  directionHi := (240890895567806873883/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree094.table
  base := (57401185330266438083861790580050113429673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-50760432062288450954613741015019655500000000000)
      constant := (1273309173509745615196184451212472742655130102069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree094.table
  base := (3587574072818715396300121319643500537659/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-50816563630475334524070219730466718000000000000)
      constant := (1276054687078519394002956062799127733997980418032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96356358227122749553/20000000000000000000)
  centralHi := (240890895567806873883/50000000000000000000)
  directionLo := (121091272508794132779/25000000000000000000)
  directionHi := (484365090035176531117/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree095.table
  base := (59457026835636153800273408068396590753663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (160446)
      previous := (80223)
      next := (80223)
      square := (1438175005728886975547853314030000000000000)
      linear := (-142105758699471760196086922753879250000000000)
      constant := (3603884877269398350576212634469830454443011899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree095.table
  base := (59457026694756855295619339300459776991811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (160446)
      previous := (80223)
      next := (80223)
      square := (1438175005728886975547853314030000000000000)
      linear := (-142262901947475353615617938194660500000000000)
      constant := (3611652814674733236149559421452273072958118703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121091272508794132779/25000000000000000000)
  centralHi := (484365090035176531117/100000000000000000000)
  directionLo := (19477387365649600801/4000000000000000000)
  directionHi := (243467342070620010013/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree096.table
  base := (61544907945862484968505699702555107543383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-3987686593748473838997001324098551000000000000)
      constant := (102230343478802101577700215039174895652602512823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree096.table
  base := (7693113478214088133111482780972634007149/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-51897251575601870786405931646078163000000000000)
      constant := (1331858023601939658113715150419988693110892648776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19477387365649600801/4000000000000000000)
  centralHi := (243467342070620010013/50000000000000000000)
  directionLo := (244745394642408799093/50000000000000000000)
  directionHi := (489490789284817598187/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree097.table
  base := (31832414314136910533158083870679274195323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-52379672546951014383134655312411916750000000000)
      constant := (1357285247081716491002567585539652320958961003038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree097.table
  base := (7958103565726807193052380816812374611887/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-52437595548165138917573787603883885500000000000)
      constant := (1360208759573344358374044114870844884727620948888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244745394642408799093/50000000000000000000)
  centralHi := (489490789284817598187/100000000000000000000)
  directionLo := (98406723138130805363/20000000000000000000)
  directionHi := (7688025245166469169/1562500000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree098.table
  base := (13163357771064259132257021675031838164407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-52919419375171868859308293411542670500000000000)
      constant := (1385874786250476609585158305067324938329615040855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree098.table
  base := (65816788767956961857141945771289754619393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-52977939520728407048741643561689608000000000000)
      constant := (1388858873996401057789987290612822468154886173229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98406723138130805363/20000000000000000000)
  centralHi := (7688025245166469169/1562500000000000000)
  directionLo := (494563368179005690367/100000000000000000000)
  directionHi := (965944078474620489/195312500000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree099.table
  base := (34000394301889477874441080060974153658441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-441811290937129944921338276947714250000000000)
      constant := (11692256881962964869143746898625193335925627226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree099.table
  base := (68000788529293502574620827485692376210673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-442299863580922935371152888590870500000000000)
      constant := (11717424519488728764176519754068074915306688389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494563368179005690367/100000000000000000000)
  centralHi := (965944078474620489/195312500000000000)
  directionLo := (248540123179089162537/50000000000000000000)
  directionHi := (19883209854327133003/4000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree100.table
  base := (70216827854068701818350451874329685092121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-53998913031613577811655569609804178000000000000)
      constant := (1443950136471725427204790973009674425293616186213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree100.table
  base := (35108413895285029193973259632707550300093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-54058627465854943311077355477301053000000000000)
      constant := (1447057238147616272637830913477251561121117420658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248540123179089162537/50000000000000000000)
  centralHi := (19883209854327133003/4000000000000000000)
  directionLo := (124896111202083613389/25000000000000000000)
  directionHi := (499584444808334453557/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree101.table
  base := (72464906589690539321274407714490187393659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-54538659859834432287829207708934931750000000000)
      constant := (1473435947503727072296049669863745090124238944127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree101.table
  base := (18116226633890883488426425206938176739899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-54598971438418211442245211435106775500000000000)
      constant := (1476605487855629000947360076155370949498877467388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124896111202083613389/25000000000000000000)
  centralHi := (499584444808334453557/100000000000000000000)
  directionLo := (251038076628524767047/50000000000000000000)
  directionHi := (100415230651409906819/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree102.table
  base := (37372512398370858444447047332702202977737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-55078406688055286764002845808065685500000000000)
      constant := (1503220515805628965367165031075057578978783777322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree102.table
  base := (74745024750607731004102831191632318354469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-55139315410981479573413067392912498000000000000)
      constant := (1506453115974413973708983876943870053499540285057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251038076628524767047/50000000000000000000)
  centralHi := (100415230651409906819/20000000000000000000)
  directionLo := (31534722296691567441/6250000000000000000)
  directionHi := (504555556747065079057/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree103.table
  base := (4816073903969430504528051767912956478277/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-55618153516276141240176483907196439250000000000)
      constant := (1533303841370780783203168955702040499130631968496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree103.table
  base := (77057182424193359294841295797131631791683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-55679659383544747704580923350718220500000000000)
      constant := (1536600122497435605929607750375053313601552566599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31534722296691567441/6250000000000000000)
  centralHi := (504555556747065079057/100000000000000000000)
  directionLo := (3961115904661394523/781250000000000000)
  directionHi := (101404567159331699789/20000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree104.table
  base := (79401379580135595365339720067136712161059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-4319838488038230439719240154332861000000000000)
      constant := (120283532630275546132428211162082957723907218179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree104.table
  base := (79401379546630526769515082172045025034113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-4324615642777539679672983023732611000000000000)
      constant := (120542039032245497179640413311426257738515089953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3961115904661394523/781250000000000000)
  centralHi := (101404567159331699789/20000000000000000000)
  directionLo := (509478166553023000783/100000000000000000000)
  directionHi := (31842385409563937549/6250000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree105.table
  base := (81777616138313200097485972513019230930407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-56697647172717850192523760105457946750000000000)
      constant := (1594366764269318236645637008190826155396211906171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree105.table
  base := (81777616109763953217096791455156857134017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-4366180563743944920532048866640743500000000000)
      constant := (122907097748850041968651092572215098395220996577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509478166553023000783/100000000000000000000)
  centralHi := (31842385409563937549/6250000000000000000)
  directionLo := (511921720939026343277/100000000000000000000)
  directionHi := (255960860469513171639/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree106.table
  base := (10523236516382115255986389356611953366971/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-57237394000938704668697398204588700500000000000)
      constant := (1625346361594021729866546236036354959536106666104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree106.table
  base := (21046473026683168704522515757002576805779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-57300691301234552098084491224135388000000000000)
      constant := (1628837412441116833813231774679545538112568089948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511921720939026343277/100000000000000000000)
  centralHi := (255960860469513171639/50000000000000000000)
  directionLo := (514353666793694472803/100000000000000000000)
  directionHi := (128588416698423618201/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree107.table
  base := (1082827594406124408488689173650659553051/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-57777140829159559144871036303719454250000000000)
      constant := (1656624716164355416025872147771007424451481060240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree107.table
  base := (10828275941470911538179903517578602615853/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-57841035273797820229252347181941110500000000000)
      constant := (1660181932534114157315632724104108691193509788872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514353666793694472803/100000000000000000000)
  centralHi := (128588416698423618201/25000000000000000000)
  directionLo := (516774168006744893939/100000000000000000000)
  directionHi := (25838708400337244697/5000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree108.table
  base := (17819712479534340642877729812649009504773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-58316887657380413621044674402850208000000000000)
      constant := (1688201827977513766964993991511531437096569311845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree108.table
  base := (5568660148751181258197447558640167888923/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-58381379246361088360420203139746833000000000000)
      constant := (1691825831011289050537527054040477193099657477104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516774168006744893939/100000000000000000000)
  centralHi := (25838708400337244697/5000000000000000000)
  directionLo := (129795846161868734619/25000000000000000000)
  directionHi := (519183384647474938477/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree109.table
  base := (45801478331225587485839848687280180268431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-4527433421969328315170639423229304750000000000)
      constant := (132313669002395355817637676907467748194548169022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree109.table
  base := (91602956647414749356210431958271850539783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-58921723218924356491588059097552555500000000000)
      constant := (1723769107870328790775634407350036573238317395899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129795846161868734619/25000000000000000000)
  centralHi := (519183384647474938477/100000000000000000000)
  directionLo := (521581473088291771413/100000000000000000000)
  directionHi := (260790736544145885707/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree110.table
  base := (47069695171671610561329006785370516244647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-490879184411753079118941740505055500000000000)
      constant := (14481424159696313561461678541914557509222256742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree110.table
  base := (94139390330536469406048357117119593666641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-491422042904856401840957975664118000000000000)
      constant := (14512493909994150793752792244147637878077546213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521581473088291771413/100000000000000000000)
  centralHi := (260790736544145885707/50000000000000000000)
  directionLo := (52396858612315390517/10000000000000000000)
  directionHi := (523968586123153905171/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree111.table
  base := (96707863437424128886825563968135159122751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-59936128142042977049565588700242469250000000000)
      constant := (1784725706852196473814169752913910848568019023603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree111.table
  base := (48353931713258662833492084426481341741373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-60002411164050892753923771013164000500000000000)
      constant := (1788553796726551532492300408889676015297477764338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52396858612315390517/10000000000000000000)
  centralHi := (523968586123153905171/100000000000000000000)
  directionLo := (526344873081178087063/100000000000000000000)
  directionHi := (65793109135147260883/12500000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree112.table
  base := (49654187971121754054472324890319992333537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-60475874970263831525739226799373223000000000000)
      constant := (1817497847616575762860387554855044088213151972122) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree112.table
  base := (19861675186591107993121903171091039376767/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-60542755136614160885091626970969723000000000000)
      constant := (1821395208720742793179167596876838205916076356255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526344873081178087063/100000000000000000000)
  centralHi := (65793109135147260883/12500000000000000000)
  directionLo := (33044404995978161963/6250000000000000000)
  directionHi := (528710479935650591409/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree113.table
  base := (101940927855749942252600446708650740621871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-61015621798484686001912864898503976750000000000)
      constant := (1850568745615226905041063742172057710944038812963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree113.table
  base := (101940927847841165162510775526112104006579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-61083099109177429016259482928775445500000000000)
      constant := (1854535999090724673591731981669933235440197904887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33044404995978161963/6250000000000000000)
  centralHi := (528710479935650591409/100000000000000000000)
  directionLo := (531065549408668105079/100000000000000000000)
  directionHi := (13276638735216702627/2500000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree114.table
  base := (26151379794057063654135069563422165495783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (160446)
      previous := (80223)
      next := (80223)
      square := (1438175005728886975547853314030000000000000)
      linear := (-170513486500569364205225770076550500000000000)
      constant := (5218665930324587069586875010407925359049466636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree114.table
  base := (104605519169494396809503055384455738854407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (160446)
      previous := (80223)
      next := (80223)
      square := (1438175005728886975547853314030000000000000)
      linear := (-170702058398173676308662988605488000000000000)
      constant := (5229850880430867844140383455731979002217982211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531065549408668105079/100000000000000000000)
  centralHi := (13276638735216702627/2500000000000000000)
  directionLo := (133352555267905117407/25000000000000000000)
  directionHi := (533410221071620469629/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree115.table
  base := (107302149902246577476685865544316374925463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-62095115454926394954260141096765484250000000000)
      constant := (1917606813311609753717060941718671792192736440939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree115.table
  base := (107302149896513535380730263736774137716457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-62163787054303965278595194844386890500000000000)
      constant := (1921715714954402688327150975188222339268453256821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133352555267905117407/25000000000000000000)
  centralHi := (533410221071620469629/100000000000000000000)
  directionLo := (267872315720857732969/50000000000000000000)
  directionHi := (535744631441715465939/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree116.table
  base := (110030820032611694524842069506825528730639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-62634862283147249430433779195896238000000000000)
      constant := (1951573983007850798369403396747867415591279548067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree116.table
  base := (13753852503466386442496775914356557385857/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-62704131026867233409763050802192613000000000000)
      constant := (1955754640446639901047110114974931391449848440168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267872315720857732969/50000000000000000000)
  centralHi := (535744631441715465939/100000000000000000000)
  directionLo := (538068914074734536271/100000000000000000000)
  directionHi := (33629307129670908517/6250000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree117.table
  base := (112791529566331365559966445305299918426107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-4859585316259084915892878253463614750000000000)
      constant := (152756916148871970731000514493649107697708279867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree117.table
  base := (28197882390544190576647815640634110305033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-4864959615340807810840838981538333500000000000)
      constant := (153084072639361841572006801793241439257686585892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538068914074734536271/100000000000000000000)
  centralHi := (33629307129670908517/6250000000000000000)
  directionLo := (270191599827098887957/50000000000000000000)
  directionHi := (108076639930839555183/20000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree118.table
  base := (288960696256456359410245205487547359167/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-63714355939588958382781055394157745500000000000)
      constant := (2020404594093596847513151259678262918561773380400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree118.table
  base := (57792139249523102314990998612529778404093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-4906524536307213051699904824446466000000000000)
      constant := (155748509734549081375367220061206027625938372666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270191599827098887957/50000000000000000000)
  centralHi := (108076639930839555183/20000000000000000000)
  directionLo := (135671904019276659939/25000000000000000000)
  directionHi := (542687616077106639757/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree119.table
  base := (59204533420342282932640559849181390450547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-64254102767809812858954693493288499250000000000)
      constant := (2055268035482247965718867159290543121402716431182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree119.table
  base := (118409066837674700515235734686816979012613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-64325162944557037803266618675609780500000000000)
      constant := (2059667687158564791270602414977349290076999329889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135671904019276659939/25000000000000000000)
  centralHi := (542687616077106639757/100000000000000000000)
  directionLo := (5449822885364235493/1000000000000000000)
  directionHi := (544982288536423549301/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree120.table
  base := (60632947290038269475889751850139384359231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-64793849596030667335128331592419253000000000000)
      constant := (2090430234100970469397546333716884009653084802086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree120.table
  base := (24253178915502989860527916257981725708551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-64865506917120305934434474633415503000000000000)
      constant := (2094904126139673354287054140054831969443889055015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5449822885364235493/1000000000000000000)
  centralHi := (544982288536423549301/100000000000000000000)
  directionLo := (547267339600438908281/100000000000000000000)
  directionHi := (273633669800219454141/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree121.table
  base := (62077380860149134394754982090162042756493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-539947077886376213316545204062396750000000000)
      constant := (17569348677268620131180015667986504675499943298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree121.table
  base := (155193452147647927596536063173686438881/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (478686)
      previous := (239343)
      next := (239343)
      square := (4290753529488662794816322697230000000000000)
      linear := (-540544222228789868310763062737365500000000000)
      constant := (17606941681753793413313550362873242459884826400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547267339600438908281/100000000000000000000)
  centralHi := (273633669800219454141/50000000000000000000)
  directionLo := (17173215290286496841/3125000000000000000)
  directionHi := (549542889289167898913/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree122.table
  base := (127075668260974176697194615706743244481653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4455462)
      previous := (2227731)
      next := (2227731)
      square := (39937013620625246013290388181910000000000000)
      linear := (-5067180250190182791344277522360058500000000000)
      constant := (166280838694433260897205704195608741630953084693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree122.table
  base := (127075668259119173919693365275614356409283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-65946194862246842196770186549026948000000000000)
      constant := (2166275139215964070806713734505954528255080579399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17173215290286496841/3125000000000000000)
  centralHi := (549542889289167898913/100000000000000000000)
  directionLo := (551809055147911797993/100000000000000000000)
  directionHi := (275904527573955898997/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree123.table
  base := (130028614201799738296389825358735737714537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-66413090080693230763649245889811514250000000000)
      constant := (2197709373335185611688350757581548405235600479061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree123.table
  base := (32507153550055333679155710471126664531647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-66486538834810110327938042506832670500000000000)
      constant := (2202409713310770410658146192067854175680907375564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551809055147911797993/100000000000000000000)
  centralHi := (275904527573955898997/50000000000000000000)
  directionLo := (277032976159055693791/50000000000000000000)
  directionHi := (554065952318111387583/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree124.table
  base := (2078337492852032035345907714023778209197/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-66952836908914085239822883988942268000000000000)
      constant := (2234066600872023626859024614013461954880337218624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree124.table
  base := (26602719908237418196373699165059282335881/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-67026882807373378459105898464638393000000000000)
      constant := (2238843665776493024891926920845781470261385167465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277032976159055693791/50000000000000000000)
  centralHi := (554065952318111387583/100000000000000000000)
  directionLo := (278156846802806653223/50000000000000000000)
  directionHi := (556313693605613306447/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree125.table
  base := (136030624282970192652708319846729917280523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-67492583737134939715996522088073021750000000000)
      constant := (2270722585638035751302023893012704087584684327119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree125.table
  base := (136030624281827631673945937410369015520629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-67567226779936646590273754422444115500000000000)
      constant := (2275576996613024696591715885702455397664185739537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278156846802806653223/50000000000000000000)
  centralHi := (556313693605613306447/100000000000000000000)
  directionLo := (69819048693307983269/12500000000000000000)
  directionHi := (558552389546463866153/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree126.table
  base := (139079688422967106264723787450901706112741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-68032330565355794192170160187203775500000000000)
      constant := (2307677327633135069889533516066678703114988315073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree126.table
  base := (69539844210997551037809874755750178574979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-68107570752499914721441610380249838000000000000)
      constant := (2312609705820281466012766803315362510933675100174) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69819048693307983269/12500000000000000000)
  centralHi := (558552389546463866153/100000000000000000000)
  directionLo := (280391074235169455991/50000000000000000000)
  directionHi := (560782148470338911983/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree127.table
  base := (71080395981201374118866278214097972097989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-68572077393576648668343798286334529250000000000)
      constant := (2344930826857254551629117267644092014804206195234) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree127.table
  base := (8885049497598493306674819451501307519383/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-68647914725063182852609466338055560500000000000)
      constant := (2349941793398198819784551125055323511254617115184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280391074235169455991/50000000000000000000)
  centralHi := (560782148470338911983/100000000000000000000)
  directionLo := (35187692285107044887/6250000000000000000)
  directionHi := (563003076561712718193/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree128.table
  base := (18159241862648540760205743779000314525989/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-69111824221797503144517436385465283000000000000)
      constant := (2382483083310343775438900822501921828836211452936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree128.table
  base := (145273934900484988215933086970608672419937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-69188258697626450983777322295861283000000000000)
      constant := (2387573259346728481343936204619949350459678485261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell102.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35187692285107044887/6250000000000000000)
  centralHi := (563003076561712718193/100000000000000000000)
  directionLo := (282607638959431823067/50000000000000000000)
  directionHi := (113043055583772729227/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree129.table
  base := (148419117239259441486392544268145026165503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-69651571050018357620691074484596036750000000000)
      constant := (2420334096992366172545315191970091296222846875059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree129.table
  base := (74209558619330603144605119969613544264533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (57921006)
      previous := (28960503)
      next := (28960503)
      square := (519181177068128198172775046364830000000000000)
      linear := (-69728602670189719114945178253667005500000000000)
      constant := (2425504103665835708471185669063214651746245715298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell102.Kernel129
