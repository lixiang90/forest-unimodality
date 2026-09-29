import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell102.Parameters
import ForestUnimodality.BinomialMassData.Q10996_21321.Batch000_049
import ForestUnimodality.BinomialMassData.Q10996_21321.Batch050_099
import ForestUnimodality.BinomialMassData.Q7339_14214.Batch000_049
import ForestUnimodality.BinomialMassData.Q7339_14214.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree000.table
  base := (4089061366615384006783173753/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (82)
      previous := (41)
      next := (41)
      square := (1146504535408193609091753700000000000000)
      linear := (-52541197015359393865385762000000000000)
      constant := (408906136661538400678317375300000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree000.table
  base := (4089061366615384006783173753/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (82)
      previous := (41)
      next := (41)
      square := (1146504535408193609091753700000000000000)
      linear := (-52541197015359393865385762000000000000)
      constant := (408906136661538400678317375300000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree001.table
  base := (229339865103115199417496602135417008692879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-24411765026150384069144006386255854000000000000)
      constant := (4539365922352921879270068053935651445249989418393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree001.table
  base := (229136845195186218317578365985072278145531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-2715370585417607661781634197583706000000000000)
      constant := (503929737956866560631598343264586388361109244453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49973352339153401089/100000000000000000000)
  directionHi := (4997335233915340109/10000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree002.table
  base := (67093675670142437678394909823436000948321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-47785076043630497369156206898616654000000000000)
      constant := (2677334931596944491161077478830536629910307884014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree002.table
  base := (133973245879310796218104397246418399764693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-5315357392094074126993067742512406000000000000)
      constant := (297017699061345440692090351000242492242451003659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49973352339153401089/100000000000000000000)
  centralHi := (4997335233915340109/10000000000000000000)
  directionLo := (70672992635279973749/100000000000000000000)
  directionHi := (56538394108223979/80000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree003.table
  base := (20650320118681314529491718506051175560587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-7906487451234512296574267490108606000000000000)
      constant := (187603363379134794991836918851603619020437475924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree003.table
  base := (16485712479731246343541822134273066719837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-879482688752282288022722365271234000000000000)
      constant := (20804219728174980180252750282844692955536334295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70672992635279973749/100000000000000000000)
  centralHi := (56538394108223979/80000000000000000)
  directionLo := (86556385275954691481/100000000000000000000)
  directionHi := (43278192637977345741/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree004.table
  base := (5367008050176147030109272619873047066417/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-94531698078590723969180607923338254000000000000)
      constant := (1159343772837006942978630551116704118383522464390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree004.table
  base := (3346410385925085821564138446452504494547/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-10515331005447007057415934832369806000000000000)
      constant := (128560590980941413819275876532111346044933895376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86556385275954691481/100000000000000000000)
  centralHi := (43278192637977345741/50000000000000000000)
  directionLo := (99946704678306802179/100000000000000000000)
  directionHi := (4997335233915340109/5000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree005.table
  base := (36663936045722456205694560395293408798943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-117905009096070837269192808435699054000000000000)
      constant := (878005283981245104964645424120625582865098452681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree005.table
  base := (36572016109785334598430033107296009383567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (7829442)
      previous := (3914721)
      next := (3914721)
      square := (109469399545309733989689735029700000000000000)
      linear := (-570231209222759718375102972926022000000000000)
      constant := (4234465437744953926404866636167840271952360727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99946704678306802179/100000000000000000000)
  centralHi := (4997335233915340109/5000000000000000000)
  directionLo := (111743812893895130061/100000000000000000000)
  directionHi := (55871906446947565031/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree006.table
  base := (13026738127699895773438464050952267566481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-15697591123727883396578334327562206000000000000)
      constant := (81681020354263523126814856507326715137697928606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree006.table
  base := (3248306475182736091831226602571271619749/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-1746144957644437776426533546914134000000000000)
      constant := (9065453372559327847581969328882520192960753944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111743812893895130061/100000000000000000000)
  centralHi := (55871906446947565031/50000000000000000000)
  directionLo := (122409213967245995979/100000000000000000000)
  directionHi := (6120460698362299799/5000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree007.table
  base := (9486488977939125527470953666567205323413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-164651631131031063869217209460420654000000000000)
      constant := (674075692764322063345657755610855507234705814342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree007.table
  base := (18922493488091040936571403248577710891367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-18315291425476406453050235467155906000000000000)
      constant := (74861554485935426983209696653114505513228088121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122409213967245995979/100000000000000000000)
  centralHi := (6120460698362299799/5000000000000000000)
  directionLo := (1322170624696078359/1000000000000000000)
  directionHi := (132217062469607835901/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree008.table
  base := (13921961702477099047279228386250696981777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-188024942148511177169229409972781454000000000000)
      constant := (665188486192580976569376154827647411293029295559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree008.table
  base := (3470577028461739560698975379925723886723/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-20915278232152872918261669012084606000000000000)
      constant := (73920791712762323161519291874426747903394286196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1322170624696078359/1000000000000000000)
  centralHi := (132217062469607835901/100000000000000000000)
  directionLo := (70672992635279973749/50000000000000000000)
  directionHi := (141345985270559947499/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree009.table
  base := (2525593997913804780453782524656806226029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-2609854977357917166286933462779534000000000000)
      constant := (8551782976073571795418556972538189267178632812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree009.table
  base := (10069914146712280368725944658000624023149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-2612807226536593264830344728557034000000000000)
      constant := (8557640715818666542721418988315164266016518043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70672992635279973749/50000000000000000000)
  centralHi := (141345985270559947499/100000000000000000000)
  directionLo := (149920057017460203269/100000000000000000000)
  directionHi := (14992005701746020327/10000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree010.table
  base := (1769900926271130539660434549325026234187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-234771564183471403769253810997503054000000000000)
      constant := (748003478217914634531848420559122183129386608116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree010.table
  base := (7052103320593859733445942446910897841491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-26115251845505805848684536101942006000000000000)
      constant := (83204126030291138196141899916594297046478249933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149920057017460203269/100000000000000000000)
  centralHi := (14992005701746020327/10000000000000000000)
  directionLo := (158029615705828023263/100000000000000000000)
  directionHi := (4938425490807125727/3125000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree011.table
  base := (4608736388274369959563989610105957165687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-258144875200951517069266011509863854000000000000)
      constant := (826275148102800264337226469019235011500350812529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree011.table
  base := (4584855885384127057828516011605865158351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-28715238652182272313895969646870706000000000000)
      constant := (91940987732051262182638369905709127057243772113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158029615705828023263/100000000000000000000)
  centralHi := (4938425490807125727/3125000000000000000)
  directionLo := (41435714806300294887/25000000000000000000)
  directionHi := (165742859225201179549/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree012.table
  base := (509055656019831947902512048127199177123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-31279798468714625596586468002469406000000000000)
      constant := (102739281618292581464905333823082879032551333745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree012.table
  base := (1262104712393879490786608982635819070937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-3479469495428748753234155910199934000000000000)
      constant := (11434800112425734904376744385839144608084249118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41435714806300294887/25000000000000000000)
  centralHi := (165742859225201179549/100000000000000000000)
  directionLo := (86556385275954691481/50000000000000000000)
  directionHi := (173112770551909382963/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree013.table
  base := (199755969900813928755405674398434486597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-304891497235911743669290412534585454000000000000)
      constant := (1041355764936007313602705189038940324421828033996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree013.table
  base := (97533380895101935467503835050007872483/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-33915212265535205244318836736728106000000000000)
      constant := (115923346632077928212193290686005381507749075432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86556385275954691481/50000000000000000000)
  centralHi := (173112770551909382963/100000000000000000000)
  directionLo := (90090742132822939073/50000000000000000000)
  directionHi := (180181484265645878147/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree014.table
  base := (-689951931467672055021349503572678342713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-328264808253391856969302613046946254000000000000)
      constant := (1175197445202201878431673438669618515525999949729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree014.table
  base := (-353361364957399768480811643856784515279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-36515199072211671709530270281656806000000000000)
      constant := (130840206573056673022557654171117810454045706846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90090742132822939073/50000000000000000000)
  centralHi := (180181484265645878147/100000000000000000000)
  directionLo := (93491581460825072863/50000000000000000000)
  directionHi := (186983162921650145727/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree015.table
  base := (-1963948219320245194739175406021210942541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-39070902141207996696590534839923006000000000000)
      constant := (147260283626126524304158720010267681433890583917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree015.table
  base := (-247370400405501430768393790007612083869/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-4346131764320904241637967091842834000000000000)
      constant := (16396788859575170417477147082736660786011015336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93491581460825072863/50000000000000000000)
  centralHi := (186983162921650145727/100000000000000000000)
  directionLo := (193545961363696583243/100000000000000000000)
  directionHi := (48386490340924145811/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree016.table
  base := (-305443574865976214889354088363229108991/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-375011430288352083569327014071667854000000000000)
      constant := (1491169081197258728153482173820048843389970781030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree016.table
  base := (-1533936350136574161971115103902919331073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-41715172685564604639953137371514206000000000000)
      constant := (166047029495010744833778258667318982530091668802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193545961363696583243/100000000000000000000)
  centralHi := (48386490340924145811/25000000000000000000)
  directionLo := (99946704678306802179/50000000000000000000)
  directionHi := (199893409356613604359/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree017.table
  base := (-3985813235511420768676177081779704069987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-398384741305832196869339214584028654000000000000)
      constant := (1672194800830967910061699519783810727668569249371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree017.table
  base := (-3997820744475366324613028759102183452039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-44315159492241071105164570916442906000000000000)
      constant := (186214478840732276528403240056033283701764877543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99946704678306802179/50000000000000000000)
  centralHi := (199893409356613604359/100000000000000000000)
  directionLo := (206045410160536864053/100000000000000000000)
  directionHi := (103022705080268432027/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree018.table
  base := (-4777566597615671026062329896629032161711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-5206889534855707532954955741930734000000000000)
      constant := (23062155318636156202232440100338951749317384023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree018.table
  base := (-299267251072314140764241307586984175623/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-5212794033213059730041778273485734000000000000)
      constant := (23114521480296159801633843553594326036140138224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206045410160536864053/100000000000000000000)
  centralHi := (103022705080268432027/50000000000000000000)
  directionLo := (212018977905839921247/100000000000000000000)
  directionHi := (6625593059557497539/3125000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree019.table
  base := (-544557523536723192164792796337672706849/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (70464978)
      previous := (35232489)
      next := (35232489)
      square := (985224595907787605907207615267300000000000000)
      linear := (-19353537536556192324754939809076098000000000000)
      constant := (90364111811300856738148490757105352504961556790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree019.table
  base := (-5455106515298968633615732274311029595203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-49515133105594004035587438006300306000000000000)
      constant := (231460825819756494302812627966032661414069714211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212018977905839921247/100000000000000000000)
  centralHi := (6625593059557497539/3125000000000000000)
  directionLo := (217828792716321607451/100000000000000000000)
  directionHi := (54457198179080401863/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree020.table
  base := (-6002950939167488814369554774869382497273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-468504674358272536769375816121111054000000000000)
      constant := (2302955624522262930031941284446254253384020474209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree020.table
  base := (-187856727356655827842715975575657980837/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-52115119912270470500798871551229006000000000000)
      constant := (256476101238334247073037120612543221844132968608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217828792716321607451/100000000000000000000)
  centralHi := (54457198179080401863/25000000000000000000)
  directionLo := (223487625787790260123/100000000000000000000)
  directionHi := (55871906446947565031/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree021.table
  base := (-1292122244278916003940926533279245501629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-54653109486194738896598668514830206000000000000)
      constant := (282395773276854142608098332054758677429780566865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree021.table
  base := (-404257009064045608459164502538666785261/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-6079456302105215218445589455128634000000000000)
      constant := (31450284540656886133859379813121674539661106768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223487625787790260123/100000000000000000000)
  centralHi := (55871906446947565031/25000000000000000000)
  directionLo := (1145033349124344749/500000000000000000)
  directionHi := (229006669824868949801/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree022.table
  base := (-1706923576600403087102385125373564036549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-515251296393232763369400217145832654000000000000)
      constant := (2794012963520704754080895628827383862283347362868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree022.table
  base := (-854291009773691770269258010012072596097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-57315093525623403431221738641086406000000000000)
      constant := (311170152552134055805052835066152644547179471112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1145033349124344749/500000000000000000)
  centralHi := (229006669824868949801/100000000000000000000)
  directionLo := (117197899691387080223/50000000000000000000)
  directionHi := (234395799382774160447/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree023.table
  base := (-888984261556190727485991000262099013913/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (70464978)
      previous := (35232489)
      next := (35232489)
      square := (985224595907787605907207615267300000000000000)
      linear := (-23418461191770125072583148593834498000000000000)
      constant := (133050302840564600406934281325053869731785244984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree023.table
  base := (-3558864922391067096535577322896848002773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (7829442)
      previous := (3914721)
      next := (3914721)
      square := (109469399545309733989689735029700000000000000)
      linear := (-2605003492708689995497094442870222000000000000)
      constant := (14817914764667350868509141243635028111694462374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117197899691387080223/50000000000000000000)
  centralHi := (234395799382774160447/100000000000000000000)
  directionLo := (119831889236862655957/50000000000000000000)
  directionHi := (47932755694745062383/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree024.table
  base := (-7319607871845772396018429872920625123057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-62444213158688109996602735352283806000000000000)
      constant := (371096259926897914489870199105499257230384075409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree024.table
  base := (-7324767708469390310301436695789725005233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-6946118570997370706849400636771534000000000000)
      constant := (41329339642908664565064146859103852570648111369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119831889236862655957/50000000000000000000)
  centralHi := (47932755694745062383/20000000000000000000)
  directionLo := (122409213967245995979/50000000000000000000)
  directionHi := (244818427934491991959/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree025.table
  base := (-3728168045727663392758092429096718647169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-585371229445673103269436818682915054000000000000)
      constant := (3633033557471418284645219749622562909635757878354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree025.table
  base := (-7460875233346224457961159983270949559829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-65115053945652802826856039275872506000000000000)
      constant := (404614271699553802565292290669408198696793246773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122409213967245995979/50000000000000000000)
  centralHi := (244818427934491991959/100000000000000000000)
  directionLo := (31233345211970875681/12500000000000000000)
  directionHi := (249866761695767005449/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree026.table
  base := (-7526646141747923612955478922173804234493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-608744540463153216569449019195275854000000000000)
      constant := (3939567951934702740609034022077699564562479390469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree026.table
  base := (-7530633145693422035856852748500745258213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-67715040752329269292067472820801206000000000000)
      constant := (438752624763978173987399831589128713866012984581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31233345211970875681/12500000000000000000)
  centralHi := (249866761695767005449/100000000000000000000)
  directionLo := (254815098736990831229/100000000000000000000)
  directionHi := (25481509873699083123/10000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree027.table
  base := (-7534408100965722937073141159416588234599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-7803924092353497899622978021081934000000000000)
      constant := (52585099164336076340674649571704004554640201807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree027.table
  base := (-942238143555812990468666971036298586381/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-7812780839889526195253211818414434000000000000)
      constant := (52707847893821267395792195237056635126663450664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254815098736990831229/100000000000000000000)
  centralHi := (25481509873699083123/10000000000000000000)
  directionLo := (64917288956966018611/25000000000000000000)
  directionHi := (51933831165572814889/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree028.table
  base := (-1496577600517627201451669492776090243221/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-655491162498113443169473420219997454000000000000)
      constant := (4592444246863448546842951453282606453949061248465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree028.table
  base := (-7485951244724033427900739651910638352003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (7829442)
      previous := (3914721)
      next := (3914721)
      square := (109469399545309733989689735029700000000000000)
      linear := (-3170218015899226183586536517854722000000000000)
      constant := (22237440494285432121714875390015836339512401557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64917288956966018611/25000000000000000000)
  centralHi := (51933831165572814889/20000000000000000000)
  directionLo := (1322170624696078359/500000000000000000)
  directionHi := (264434124939215671801/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree029.table
  base := (-7374842750267728069323014001194888407673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-678864473515593556469485620732358254000000000000)
      constant := (4938667106584428159831227449547478564009023677409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree029.table
  base := (-7377522691390457990995946493084375496089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-75515001172358668687701773455587306000000000000)
      constant := (550018083803095261655012071874304921094932302393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1322170624696078359/500000000000000000)
  centralHi := (264434124939215671801/100000000000000000000)
  directionLo := (269114738311341641067/100000000000000000000)
  directionHi := (67278684577835410267/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree030.table
  base := (-7212599865157365922115384095000956572609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-78026420503674852196610869027191006000000000000)
      constant := (588668401002932363274618108455581594306286561633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree030.table
  base := (-721494176841521949441133604772103170373/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-8679443108781681683657023000057334000000000000)
      constant := (65559598719429538075833168243270004217067953890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269114738311341641067/100000000000000000000)
  centralHi := (67278684577835410267/25000000000000000000)
  directionLo := (273715323503078762377/100000000000000000000)
  directionHi := (136857661751539381189/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree031.table
  base := (-1399624920189471401227198264195074364973/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-725611095550553783069510021757079854000000000000)
      constant := (5670450911801103797105586723548661782217543441545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree031.table
  base := (-1400033780365860818921107870907881248537/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-80714974785711601618124640545444706000000000000)
      constant := (631511740164805796330190450260957663908470450845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273715323503078762377/100000000000000000000)
  centralHi := (136857661751539381189/50000000000000000000)
  directionLo := (278239850245086621801/100000000000000000000)
  directionHi := (139119925122543310901/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree032.table
  base := (-3366538243558417097780129091297638974443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-748984406568033896369522222269440654000000000000)
      constant := (6055940215026986945939755984069479123095620077638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree032.table
  base := (-6734859203701860732439225034075076710317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-83314961592388068083336074090373406000000000000)
      constant := (674440504142539211167574577576068576814311118029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278239850245086621801/100000000000000000000)
  centralHi := (139119925122543310901/50000000000000000000)
  directionLo := (282691970541119894997/100000000000000000000)
  directionHi := (141345985270559947499/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree033.table
  base := (-6418856997966847202123526543510440181759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-85817524176168223296614935864644606000000000000)
      constant := (717161757685702093419571878570075080203125785183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree033.table
  base := (-321020506474654600402464698517290353709/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-9546105377673837172060834181700234000000000000)
      constant := (79868845723092865365776272574300452653250560740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282691970541119894997/100000000000000000000)
  centralHi := (141345985270559947499/50000000000000000000)
  directionLo := (287075053169784446951/100000000000000000000)
  directionHi := (35884381646223055869/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree034.table
  base := (-6056649758231490929258165136629235579939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-795731028602994122969546623294162254000000000000)
      constant := (6865974330403739605711511910941978855221511778587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree034.table
  base := (-1211600333201372767083534030985550017679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-88514935205741001013758941180230806000000000000)
      constant := (764646470935335069512769191092151454357629011115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287075053169784446951/100000000000000000000)
  centralHi := (35884381646223055869/12500000000000000000)
  directionLo := (4553003336152474261/1562500000000000000)
  directionHi := (58278442702751670541/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree035.table
  base := (-1411863616050281889090373267198129643521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-819104339620474236269558823806523054000000000000)
      constant := (7290475990159938725996886662395852297543772318372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree035.table
  base := (-2824315115439128667869076039672959255277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-91114922012417467478970374725159506000000000000)
      constant := (811918894229136105677670574649716824157957251098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4553003336152474261/1562500000000000000)
  centralHi := (58278442702751670541/20000000000000000000)
  directionLo := (73911584866844835779/25000000000000000000)
  directionHi := (295646339467379343117/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree036.table
  base := (-5192115508942865511098015335507089036149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-10400958649851288266291000300233134000000000000)
      constant := (95406717399710703723671992580083545725556390957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree036.table
  base := (-5193137273771295433594249769798075468761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-10412767646565992660464645363343134000000000000)
      constant := (95626114834751708178984551895859804999094034673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73911584866844835779/25000000000000000000)
  centralHi := (295646339467379343117/100000000000000000000)
  directionLo := (149920057017460203269/50000000000000000000)
  directionHi := (299840114034920406539/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree037.table
  base := (-586418267798917362478806036384971639089/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-865850961655434462869583224831244654000000000000)
      constant := (8178364590977503611157455087028030569969005124296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree037.table
  base := (-938446682257351858028977012663882153879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-96314895625770400409393241815016906000000000000)
      constant := (910793328227398712033222222965010706827530108115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149920057017460203269/50000000000000000000)
  centralHi := (299840114034920406539/100000000000000000000)
  directionLo := (303976035121993197663/100000000000000000000)
  directionHi := (9499251097562287427/3125000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree038.table
  base := (-4145748865427701979221026724702854854029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-889224272672914576169595425343605454000000000000)
      constant := (8641725526793715422273821790658920622146268609557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree038.table
  base := (-518314849452424596843864989112232563479/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-98914882432446866874604675359945606000000000000)
      constant := (962392460401006866354522119773469663759588934584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303976035121993197663/100000000000000000000)
  centralHi := (9499251097562287427/3125000000000000000)
  directionLo := (15402821646738984003/5000000000000000000)
  directionHi := (308056432934779680061/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree039.table
  base := (-1777916323399470110383747630379983382583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-101399731521154965496623069539551806000000000000)
      constant := (1013112984142033526063009749544657469105789258542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree039.table
  base := (-711300061297800439081019944658638679749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-11279429915458148148868456544986034000000000000)
      constant := (112825701877087971769707465004033573758352428785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15402821646738984003/5000000000000000000)
  centralHi := (308056432934779680061/100000000000000000000)
  directionLo := (78020871332817725183/25000000000000000000)
  directionHi := (312083485331270900733/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree040.table
  base := (-2922027459148949894429574125326831062189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-935970894707874802769619826368327054000000000000)
      constant := (9607230084208134093068583975047491610573684342837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree040.table
  base := (-584521212618142502458636220510072183581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-104114856045799799805027542449803006000000000000)
      constant := (1069908957529029320693561005539575186751542791985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78020871332817725183/25000000000000000000)
  centralHi := (312083485331270900733/100000000000000000000)
  directionLo := (316059231411656046527/100000000000000000000)
  directionHi := (4938425490807125727/1562500000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree041.table
  base := (-2244696552578128265566175127311131043097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-959344205725354916069632026880687854000000000000)
      constant := (10109358028102265439300507486601396684652929456001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree041.table
  base := (-561299418699936006506471909960583409569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-106714842852476266270238975994731706000000000000)
      constant := (1125824588189750225018335493805878771263326692612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316059231411656046527/100000000000000000000)
  centralHi := (4938425490807125727/1562500000000000000)
  directionLo := (159992791794302343249/50000000000000000000)
  directionHi := (319985583588604686499/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree042.table
  base := (-762073409305084143570286686840032952047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (7829442)
      previous := (3914721)
      next := (3914721)
      square := (109469399545309733989689735029700000000000000)
      linear := (-4747427617115145069418571146826322000000000000)
      constant := (51325577890737265757519747735133077627411200786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree042.table
  base := (-1524580583707986993778664090692521970109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-12146092184350303637272267726628934000000000000)
      constant := (131464170900653090678649685677673767791639613237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159992791794302343249/50000000000000000000)
  centralHi := (319985583588604686499/100000000000000000000)
  directionLo := (161932169170113544167/50000000000000000000)
  directionHi := (64772867668045417667/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree043.table
  base := (-760637542237360586342844153532614547959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1006090827760315142669656427905409454000000000000)
      constant := (11152334745393577588002254593974501625081689631247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree043.table
  base := (-190253199192915092750567310125143474941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-111914816465829199200661843084589106000000000000)
      constant := (1241967240677881798894131977728589496179962570868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161932169170113544167/50000000000000000000)
  centralHi := (64772867668045417667/20000000000000000000)
  directionLo := (327697185817282010857/100000000000000000000)
  directionHi := (163848592908641005429/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree044.table
  base := (712690731424806290145252250243311933/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1029464138777795255969668628417770254000000000000)
      constant := (11693174064316817556105836594167585997120107392704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree044.table
  base := (5660967655667983890530913869412817797/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-114514803272505665665873276629517806000000000000)
      constant := (1302193217285330146483286536493217798567117865688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327697185817282010857/100000000000000000000)
  centralHi := (163848592908641005429/50000000000000000000)
  directionLo := (41435714806300294887/12500000000000000000)
  directionHi := (331485718450402359097/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree045.table
  base := (223604332914611826892890463856943204279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-12997993207349078632959022579384334000000000000)
      constant := (151196406441885264027639736569477644561786023812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree045.table
  base := (223534230530404338937441131988286838953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-13012754453242459125676078908271834000000000000)
      constant := (151539451512774425347890893775319793626849618684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41435714806300294887/12500000000000000000)
  centralHi := (331485718450402359097/100000000000000000000)
  directionLo := (41903929835210673773/12500000000000000000)
  directionHi := (67046287736337078037/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree046.table
  base := (1785621435881990162506555203293571958331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (70464978)
      previous := (35232489)
      next := (35232489)
      square := (985224595907787605907207615267300000000000000)
      linear := (-46791772209250238372595349106195298000000000000)
      constant := (557110270726681497071981842475544869897380619899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree046.table
  base := (1785379217022623802158464554363115504257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (7829442)
      previous := (3914721)
      next := (3914721)
      square := (109469399545309733989689735029700000000000000)
      linear := (-5204990299385156460708527987798922000000000000)
      constant := (62041410352855734156047342568434106631461962617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41903929835210673773/12500000000000000000)
  centralHi := (67046287736337078037/20000000000000000000)
  directionLo := (338935765927123365897/100000000000000000000)
  directionHi := (169467882963561682949/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree047.table
  base := (108763694807374859295916531554421706359/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1099584071830235595869705229954852654000000000000)
      constant := (13393053367206078346951118520668407837039669538825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree047.table
  base := (2718883236961729748393640291744398860277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-122314763692535065061507577264303906000000000000)
      constant := (1491485052248974165617134009720813511794296489451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338935765927123365897/100000000000000000000)
  centralHi := (169467882963561682949/50000000000000000000)
  directionLo := (68520008572275858729/20000000000000000000)
  directionHi := (171300021430689646823/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree048.table
  base := (3694718470719283375359349711538476003279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-124773042538635078796635270051912606000000000000)
      constant := (1553939792920260699899290203263851408227188890577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree048.table
  base := (923634495887353497625900948089815168839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-13879416722134614614079890089914734000000000000)
      constant := (173050295806154486790159964469865838119611591492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68520008572275858729/20000000000000000000)
  centralHi := (171300021430689646823/50000000000000000000)
  directionLo := (13849021644152750637/4000000000000000000)
  directionHi := (173112770551909382963/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree049.table
  base := (4712405381516495528181775096971557203847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1146330693865195822469729630979574254000000000000)
      constant := (14590748669037582822052210271107852935449766689249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree049.table
  base := (4712249682566302249799718398591535450047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-127514737305887997991930444354161306000000000000)
      constant := (1624855062200837010335426087113687017115036564961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13849021644152750637/4000000000000000000)
  centralHi := (173112770551909382963/50000000000000000000)
  directionLo := (87453366593518451907/25000000000000000000)
  directionHi := (349813466374073807629/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree050.table
  base := (1443018342550557823674364328023938130097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1169704004882675935769741831491935054000000000000)
      constant := (15208923389595944338260696410885981611104627491996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree050.table
  base := (1154387821930697421875630544220812710907/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-130114724112564464457141877899090006000000000000)
      constant := (1693692078103630757990405151703135003121762795705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87453366593518451907/25000000000000000000)
  centralHi := (349813466374073807629/100000000000000000000)
  directionLo := (176682481588199934373/50000000000000000000)
  directionHi := (353364963176399868747/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree051.table
  base := (6873655060349834804985464854382611777641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-132564146211128449896639336889366206000000000000)
      constant := (1759997885143503554132452745924990497568241627383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree051.table
  base := (3436769665776223831930429539469957943051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (869938)
      previous := (434969)
      next := (434969)
      square := (12163266616145525998854415003300000000000000)
      linear := (-641133869175076960977552229198158000000000000)
      constant := (8521563106155164815851930639964981567635656118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176682481588199934373/50000000000000000000)
  centralHi := (353364963176399868747/100000000000000000000)
  directionLo := (89220279766104607553/25000000000000000000)
  directionHi := (356881119064418430213/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree052.table
  base := (2004273378931972984983815432542223893133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1216450626917636162369766232516656654000000000000)
      constant := (16483920273804385256984439009371982865859312073644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree052.table
  base := (8016993798257299106611967062626667022623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-135314697725917397387564744988947406000000000000)
      constant := (1835669392624926513602144369943498318261702533249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89220279766104607553/25000000000000000000)
  centralHi := (356881119064418430213/100000000000000000000)
  directionLo := (90090742132822939073/25000000000000000000)
  directionHi := (360362968531291756293/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree053.table
  base := (2300585155446125755075255440070642892289/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1239823937935116275669778433029017454000000000000)
      constant := (17140740361171219451450056658038587136710878895452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree053.table
  base := (9202254731509982688571187529186672597769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-137914684532593863852776178533876106000000000000)
      constant := (1908809462131988220882151748359181489785074383447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90090742132822939073/25000000000000000000)
  centralHi := (360362968531291756293/100000000000000000000)
  directionLo := (9095287414119259889/2500000000000000000)
  directionHi := (363811496564770395561/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree054.table
  base := (10429355718208093813729521591581736572033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-15595027764846868999627044858535534000000000000)
      constant := (219881980552575089145655664304883820795732056231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree054.table
  base := (10429281763565871579635592879666571302757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-15612741259918925590887512453200534000000000000)
      constant := (220375964760577096698997272469784487063871827299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9095287414119259889/2500000000000000000)
  centralHi := (363811496564770395561/100000000000000000000)
  directionLo := (367227641901737987937/100000000000000000000)
  directionHi := (183613820950868993969/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree055.table
  base := (11698104443582276118932570423798034697823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1286570559970076502269802834053739054000000000000)
      constant := (18493019785427957145526225527962302371253447437641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree055.table
  base := (584902039366442618421022885974265736799/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-143114658145946796783199045623733506000000000000)
      constant := (2059391979863211649722069707345935158735040446740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367227641901737987937/100000000000000000000)
  centralHi := (183613820950868993969/50000000000000000000)
  directionLo := (46326537501590995283/12500000000000000000)
  directionHi := (74122460002545592453/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree056.table
  base := (13008557759211664030782091956621491304577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1309943870987556615569815034566099854000000000000)
      constant := (19188477869242103678321647308220137182529229523159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree056.table
  base := (13008502985008419065402993801367195986431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-145714644952623263248410479168662206000000000000)
      constant := (2136834289900358087220565130786128784519549621153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46326537501590995283/12500000000000000000)
  centralHi := (74122460002545592453/20000000000000000000)
  directionLo := (93491581460825072863/25000000000000000000)
  directionHi := (373966325843300291453/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree057.table
  base := (7180345562155828300348401046260003995641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-148146353556115192096647470564273406000000000000)
      constant := (2210757132351448926796430644997487358309358722766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree057.table
  base := (574425760302455088454176673761418404561/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-16479403528811081079291323634843434000000000000)
      constant := (246190062164955593114749375650394198516042898175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93491581460825072863/25000000000000000000)
  centralHi := (373966325843300291453/100000000000000000000)
  directionLo := (37729053633605841631/10000000000000000000)
  directionHi := (377290536336058416311/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree058.table
  base := (1575448379907515101265563051639550021639/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1356690493022516842169839435590821454000000000000)
      constant := (20618028341277460083381773900579582294525354653130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree058.table
  base := (787722164074736054537205342053978957571/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-150914618565976196178833346258519606000000000000)
      constant := (2296020743435251631547942137585054241830004859460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37729053633605841631/10000000000000000000)
  centralHi := (377290536336058416311/100000000000000000000)
  directionLo := (95146428188596425909/25000000000000000000)
  directionHi := (380585712754385703637/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree059.table
  base := (17189918255777079692520869357622109411557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1380063804039996955469851636103182254000000000000)
      constant := (21352119973157466449314769400591313278146048900819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree059.table
  base := (17189883423248372601400487482997805730301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-153514605372652662644044779803448306000000000000)
      constant := (2377764803576918871968869182595674814245502004963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95146428188596425909/25000000000000000000)
  centralHi := (380585712754385703637/100000000000000000000)
  directionLo := (383852602826627910773/100000000000000000000)
  directionHi := (191926301413313955387/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree060.table
  base := (4666744920289574156914701263573165346529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-155937457228608563196651537401727006000000000000)
      constant := (2455454310447267395470820047428828464841578061308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree060.table
  base := (4666737436112892447022375661889197491927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-17346065797703236567695134816486334000000000000)
      constant := (273438078628112722075980927655049929649650525956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383852602826627910773/100000000000000000000)
  centralHi := (191926301413313955387/50000000000000000000)
  directionLo := (387091922727393166487/100000000000000000000)
  directionHi := (48386490340924145811/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree061.table
  base := (10092827777966020458443162807973595554337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1426810426074957182069876037127903854000000000000)
      constant := (22858934556442998435105192983180061671129191554158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree061.table
  base := (20185629833943190264086049954923918058831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-158714578986005595574467646893305706000000000000)
      constant := (2545554428407846783780860947976815550264030582353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387091922727393166487/100000000000000000000)
  centralHi := (48386490340924145811/12500000000000000000)
  directionLo := (97576089727710475031/25000000000000000000)
  directionHi := (3122434871286735201/800000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree062.table
  base := (4349187059890710434959787554347020081343/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1450183737092437295369888237640264654000000000000)
      constant := (23631657051288379807081934140200353946240245867405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree062.table
  base := (10872956602319397203996197480958091765551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-161314565792682062039679080438234406000000000000)
      constant := (2631599942811117611531681406945273561753862451426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97576089727710475031/25000000000000000000)
  centralHi := (3122434871286735201/800000000000000000)
  directionLo := (196745284904630217461/50000000000000000000)
  directionHi := (393490569809260434923/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree063.table
  base := (11673904984724670164464562109816683610913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-18192062322344659366295067137686734000000000000)
      constant := (301447606195325767263043022183714071035696096782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree063.table
  base := (11673895497589313372904137908183063661767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-18212728066595392056098945998129234000000000000)
      constant := (302119914600302521472310032084107441629833560738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196745284904630217461/50000000000000000000)
  centralHi := (393490569809260434923/100000000000000000000)
  directionLo := (3966511874088235077/1000000000000000000)
  directionHi := (396651187408823507701/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree064.table
  base := (12495636004135121944650652499776740774251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1496930359127397521969912638664986254000000000000)
      constant := (25215731558668357244016402774736492412148631528634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree064.table
  base := (1249562785892717230180292678381675604987/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-166514539406034994970101947528091806000000000000)
      constant := (2807992277739182782800653601622435937482291323620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3966511874088235077/1000000000000000000)
  centralHi := (396651187408823507701/100000000000000000000)
  directionLo := (399786818713227208717/100000000000000000000)
  directionHi := (199893409356613604359/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree065.table
  base := (5335263005691317540224654978444965285151/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (70464978)
      previous := (35232489)
      next := (35232489)
      square := (985224595907787605907207615267300000000000000)
      linear := (-66100159571516418924779340833797698000000000000)
      constant := (1131612317199300668905067920114490787867617618395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree065.table
  base := (3334537630704085550288494137416235650633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-169114526212711461435313381073020506000000000000)
      constant := (2898339067925934230266012387124059075693088463032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399786818713227208717/100000000000000000000)
  centralHi := (199893409356613604359/50000000000000000000)
  directionLo := (50362255888099119833/12500000000000000000)
  directionHi := (80579609420958591733/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree066.table
  base := (28402933631522328571999896408633140679597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-171519664573595305396659671076634206000000000000)
      constant := (2983479022874369163496219486132821416820257826611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree066.table
  base := (2840292163220946819988943627932106754873/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-19079390335487547544502757179772134000000000000)
      constant := (332235510024684027080329899371107489729362961110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50362255888099119833/12500000000000000000)
  centralHi := (80579609420958591733/20000000000000000000)
  directionLo := (405985433611686534467/100000000000000000000)
  directionHi := (101496358402921633617/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree067.table
  base := (3017112325481001439759383083536773922953/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1567050292179837861869949240202068654000000000000)
      constant := (27688415199345629593799176090819907019640574063510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree067.table
  base := (30171112959969236726703357501096616098327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-174314499826064394365736248162877906000000000000)
      constant := (3083333834706880664841445042960690790038740286601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405985433611686534467/100000000000000000000)
  centralHi := (101496358402921633617/25000000000000000000)
  directionLo := (8180990361780957463/2000000000000000000)
  directionHi := (409049518089047873151/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree068.table
  base := (15990440021033331701398959429032593087573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1590423603197317975169961440714429454000000000000)
      constant := (28538395199795666324572279927058420734526146851782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree068.table
  base := (999402225360041644318562075754416593937/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-176914486632740860830947681707806606000000000000)
      constant := (3177981792996877114437461882147446391792994240992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8180990361780957463/2000000000000000000)
  centralHi := (409049518089047873151/100000000000000000000)
  directionLo := (206045410160536864053/50000000000000000000)
  directionHi := (412090820321073728107/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree069.table
  base := (3383220073406507943188397962687370022029/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (7829442)
      previous := (3914721)
      next := (3914721)
      square := (109469399545309733989689735029700000000000000)
      linear := (-7796120358525594630289727735395122000000000000)
      constant := (142035029675373035638373211689448895770733509490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree069.table
  base := (16916096580577605294153276362583090592947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (869938)
      previous := (434969)
      next := (434969)
      square := (12163266616145525998854415003300000000000000)
      linear := (-867219678451291436213329059191958000000000000)
      constant := (15816731681199430025596571569177590016201149446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206045410160536864053/50000000000000000000)
  centralHi := (412090820321073728107/100000000000000000000)
  directionLo := (103777460262606109113/25000000000000000000)
  directionHi := (415109841050424436453/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree070.table
  base := (17862541288082448415843591607184356914643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1637170225232278201769985841739151054000000000000)
      constant := (30276982973921011683655625725648221087182749709162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree070.table
  base := (8931269020781334174151192410671231712617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-182114460246093793761370548797664006000000000000)
      constant := (3371578823755186452922694007763345258514019307484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103777460262606109113/25000000000000000000)
  centralHi := (415109841050424436453/100000000000000000000)
  directionLo := (83621412588145581817/20000000000000000000)
  directionHi := (209053531470363954543/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree071.table
  base := (18829761620094521084361133460610532222749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1660543536249758315069998042251511854000000000000)
      constant := (31165590647136634488369353126721827634044363069366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree071.table
  base := (37659517674155481540530564272539636542797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-184714447052770260226581982342592706000000000000)
      constant := (3470527885179450721139603071722074987845084408211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83621412588145581817/20000000000000000000)
  centralHi := (209053531470363954543/50000000000000000000)
  directionLo := (421082951477419681591/100000000000000000000)
  directionHi := (52635368934677460199/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree072.table
  base := (39635520758398031537149227772480518850423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-20789096879842449732963089416837934000000000000)
      constant := (395889803994537875593605439418001701963135164961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree072.table
  base := (39635515987957211746030147879076107811081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-20812714873271858521310379543057934000000000000)
      constant := (396767848667433644898721424582640371838658441567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421082951477419681591/100000000000000000000)
  centralHi := (52635368934677460199/12500000000000000000)
  directionLo := (84807591162335968499/20000000000000000000)
  directionHi := (6625593059557497539/1562500000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree073.table
  base := (10413268366922045142866741875168112524487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1707290158284718541670022443276233454000000000000)
      constant := (32981433370313287790204889178776065577015049808516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree073.table
  base := (41653069379899508490283398764861848565083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-189914420666123193157004849432450106000000000000)
      constant := (3672727078625829372680264431413181643745381868229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84807591162335968499/20000000000000000000)
  centralHi := (6625593059557497539/1562500000000000000)
  directionLo := (42697250955179926597/10000000000000000000)
  directionHi := (426972509551799265971/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree074.table
  base := (8742435992486035551295690723290043502017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1730663469302198654970034643788594254000000000000)
      constant := (33908668359622139385131915617638742322142648158195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree074.table
  base := (43712176460255459455514806340164440924999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (7829442)
      previous := (3914721)
      next := (3914721)
      square := (109469399545309733989689735029700000000000000)
      linear := (-8370191629252159114009403607712122000000000000)
      constant := (164172921912360981507374211352961318983959829519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42697250955179926597/10000000000000000000)
  centralHi := (426972509551799265971/100000000000000000000)
  directionLo := (214943515752961529133/50000000000000000000)
  directionHi := (429887031505923058267/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree075.table
  base := (22906419527304913981544757235828035603347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-194892975591075418696671871588995006000000000000)
      constant := (3872086563111504061253673833844072646702386045722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree075.table
  base := (45812836054696130907236053604563188499591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-21679377142164014009714190724700834000000000000)
      constant := (431184556833713565428084277051294949936219701137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214943515752961529133/50000000000000000000)
  centralHi := (429887031505923058267/100000000000000000000)
  directionLo := (432781926379773457407/100000000000000000000)
  directionHi := (422638599980247517/97656250000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree076.table
  base := (4795504974014009603944542283658908854107/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1777410091337158881570059044813315854000000000000)
      constant := (35801765475612133808568147909051651795938910266690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree076.table
  base := (47955047170907996240125837352936016921663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-197714381086152592552639150067236206000000000000)
      constant := (3986778499004004895052257611363264284129038012769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432781926379773457407/100000000000000000000)
  centralHi := (422638599980247517/97656250000000000)
  directionLo := (217828792716321607451/50000000000000000000)
  directionHi := (435657585432643214903/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree077.table
  base := (50138811170388769095886031517995994155773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1800783402354638994870071245325676654000000000000)
      constant := (36767627565675082926971214244572819940223383895291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree077.table
  base := (2506940448519228006540080274168805983361/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-200314367892829059017850583612164906000000000000)
      constant := (4094329664644637903628750757306369773484754154860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217828792716321607451/50000000000000000000)
  centralHi := (435657585432643214903/100000000000000000000)
  directionLo := (438514387094669894177/100000000000000000000)
  directionHi := (219257193547334947089/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree078.table
  base := (409094708032141362371492218354461274867/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-202684079263568789796675938426448606000000000000)
      constant := (4194040591557379025454442135049878389205535823488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree078.table
  base := (26182060372295021382251137418127531115629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-22546039411056169498118001906343734000000000000)
      constant := (467034945207703544928321584747131990969862570806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438514387094669894177/100000000000000000000)
  centralHi := (219257193547334947089/50000000000000000000)
  directionLo := (441352697548148173701/100000000000000000000)
  directionHi := (220676348774074086851/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree079.table
  base := (5463098350712584744746924293709655764091/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1847530024389599221470095646350398254000000000000)
      constant := (38737978738655031408939128088133139914963127635970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree079.table
  base := (5463098189481737370557263604118002320709/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-205514341506181991948273450702022306000000000000)
      constant := (4313733024363288452008551841561145749304231686670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441352697548148173701/100000000000000000000)
  centralHi := (220676348774074086851/50000000000000000000)
  directionLo := (55521608909426022859/12500000000000000000)
  directionHi := (444172871275408182873/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree080.table
  base := (28469696647547499648878027535906450979711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1870903335407079334770107846862759054000000000000)
      constant := (39742467799464982047003142517461776232241427400274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree080.table
  base := (56939391915167835058852930311573809550481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-208114328312858458413484884246951006000000000000)
      constant := (4425585216015522090472725268457116194922857956303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55521608909426022859/12500000000000000000)
  centralHi := (444172871275408182873/100000000000000000000)
  directionLo := (223487625787790260123/50000000000000000000)
  directionHi := (446975251575580520247/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree081.table
  base := (59289351559024486620020177512719257029441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-23386131437340240099631111695989134000000000000)
      constant := (503207808615904489809894991664236991749982810087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree081.table
  base := (59289350378168483168533369507764151133931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-23412701679948324986521813087986634000000000000)
      constant := (504319008987475033853756214737858461225737101517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223487625787790260123/50000000000000000000)
  centralHi := (446975251575580520247/100000000000000000000)
  directionLo := (449760171052380609807/100000000000000000000)
  directionHi := (28110010690773788113/6250000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree082.table
  base := (15420214483242271083927760404267362233411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1917649957442039561370132247887480654000000000000)
      constant := (41790072826692127372339090533329744395102085392148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree082.table
  base := (61680856922618496725491163250785169351877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-213314301926211391343907751336808406000000000000)
      constant := (4653590618185328335395217711703972673362391060251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449760171052380609807/100000000000000000000)
  centralHi := (28110010690773788113/6250000000000000000)
  directionLo := (452527952074874413227/100000000000000000000)
  directionHi := (113131988018718603307/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree083.table
  base := (64113912107656180157277479174056873724453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1941023268459519674670144448399841454000000000000)
      constant := (42833188779763933873393602813010663174537490856851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree083.table
  base := (100177986317685911785657368977826231313/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-215914288732887857809119184881737106000000000000)
      constant := (4769743827239445187834308143107303432490189260160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452527952074874413227/100000000000000000000)
  centralHi := (113131988018718603307/25000000000000000000)
  directionLo := (455278907213032440589/100000000000000000000)
  directionHi := (45527890721303244059/10000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree084.table
  base := (16647128455428292137653400463216157897343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-218266286608555531996684072101355806000000000000)
      constant := (4876575594659751867080180505426333765442051042436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree084.table
  base := (66588513082394333422200385987719812656311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-24279363948840480474925624269629534000000000000)
      constant := (543036745275923863982457822922758504326828478177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455278907213032440589/100000000000000000000)
  centralHi := (45527890721303244059/10000000000000000000)
  directionLo := (1145033349124344749/250000000000000000)
  directionHi := (458013339649737899601/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree085.table
  base := (69104662854252748087919210037563404188481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-1987769890494479901270168849424563054000000000000)
      constant := (44958047538847884294804203032886357258831313352727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree085.table
  base := (69104662221958455291390667518460158335761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-221114262346240790739542051971594506000000000000)
      constant := (5006351258438445516600278996661015180695306308943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1145033349124344749/250000000000000000)
  centralHi := (458013339649737899601/100000000000000000000)
  directionLo := (115182885892696570957/25000000000000000000)
  directionHi := (460731543570786283829/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree086.table
  base := (14332471803721183100465357564306483451787/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-2011143201511960014570181049936923854000000000000)
      constant := (46039790336804854324750116366898751247586177156145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree086.table
  base := (71662358477917471300657159201505033680007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-223714249152917257204753485516523206000000000000)
      constant := (5126805479700555656436462635134364114778417212441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115182885892696570957/25000000000000000000)
  centralHi := (460731543570786283829/100000000000000000000)
  directionLo := (115858451133574117817/25000000000000000000)
  directionHi := (463433804534296471269/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree087.table
  base := (2970464086280999808519885643713647578691/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-226057390281048903096688138938809406000000000000)
      constant := (5237156526965651376716400486958103373065072338325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree087.table
  base := (74261601694732747069907886443399995246409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-25146026217732635963329435451272434000000000000)
      constant := (583188152325341395035335933302583110640090520863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115858451133574117817/25000000000000000000)
  centralHi := (463433804534296471269/100000000000000000000)
  directionLo := (233060199910423185321/50000000000000000000)
  directionHi := (466120399820846370643/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree088.table
  base := (19225598034051637144352191571334717272467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (70464978)
      previous := (35232489)
      next := (35232489)
      square := (985224595907787605907207615267300000000000000)
      linear := (-89473470588996532224791541346158498000000000000)
      constant := (2097474032777009728152876598864563789036127178572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree088.table
  base := (38451195870497717580041301067687220863669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-228914222766270190135176352606380606000000000000)
      constant := (5372014931832414105511396326981238730623063070294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233060199910423185321/50000000000000000000)
  centralHi := (466120399820846370643/100000000000000000000)
  directionLo := (468791598765548320893/100000000000000000000)
  directionHi := (234395799382774160447/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree089.table
  base := (127335566149611605377182286060774917603/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-2081263134564400354470217651474006254000000000000)
      constant := (49362272368119591906543044869341720212802483063125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree089.table
  base := (79584728505686774836211750247821631921271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-231514209572946656600387786151309306000000000000)
      constant := (5496770162169776114260661968785290050461922156073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468791598765548320893/100000000000000000000)
  centralHi := (234395799382774160447/50000000000000000000)
  directionLo := (471447663073189932941/100000000000000000000)
  directionHi := (235723831536594966471/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree090.table
  base := (82308612183745490621512221169458106724329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-25983165994838030466299133975140334000000000000)
      constant := (623401451648823992380135727160056524247483346303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree090.table
  base := (82308611895017881527675931773959467190461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-26012688486624791451733246632915334000000000000)
      constant := (624773229081576920261001352877152337710742817227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471447663073189932941/100000000000000000000)
  centralHi := (235723831536594966471/50000000000000000000)
  directionLo := (474088847117484069791/100000000000000000000)
  directionHi := (14815276472421377181/3125000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree091.table
  base := (85074042076497980903492478342129753254807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-2128009756599360581070242052498727854000000000000)
      constant := (51641638398587146881087505613056008694898101023569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree091.table
  base := (212685104574398071269263914351501090379/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-236714183186299589530810653241166706000000000000)
      constant := (5750581630351669577624277162007760611616391150800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474088847117484069791/100000000000000000000)
  centralHi := (14815276472421377181/3125000000000000000)
  directionLo := (476715398225396482833/100000000000000000000)
  directionHi := (238357699112698241417/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree092.table
  base := (87881018453814845423622686781527220340809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (70464978)
      previous := (35232489)
      next := (35232489)
      square := (985224595907787605907207615267300000000000000)
      linear := (-93538394244210464972619750130916898000000000000)
      constant := (2295679774429295759547085704347464220728247057161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree092.table
  base := (2197025456074598491108783962296930562301/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (7829442)
      previous := (3914721)
      next := (3914721)
      square := (109469399545309733989689735029700000000000000)
      linear := (-10404963912738089391131395077656322000000000000)
      constant := (255636429038053581030760868063116253080762471240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476715398225396482833/100000000000000000000)
  centralHi := (238357699112698241417/50000000000000000000)
  directionLo := (119831889236862655957/25000000000000000000)
  directionHi := (479327556947450623829/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree093.table
  base := (11341192657286041124188016642565557252743/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-241639597626035645296696272613716606000000000000)
      constant := (5996945202475563413837409629789835170857044406472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree093.table
  base := (45364770539080385700450420982764290996773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-26879350755516946940137057814558234000000000000)
      constant := (667791974908970496480413021497321894706499178822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119831889236862655957/25000000000000000000)
  centralHi := (479327556947450623829/100000000000000000000)
  directionLo := (96385111462969152807/20000000000000000000)
  directionHi := (120481389328711441009/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree094.table
  base := (23404902610355111542533871170571209001573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-2198129689651800920970278654035810254000000000000)
      constant := (55157254428847409963295427495440026130330370655564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree094.table
  base := (748956882300340791893631563808706637721/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-244514143606328988926444953875952806000000000000)
      constant := (6142051349163320197363799479900693379619186552875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96385111462969152807/20000000000000000000)
  centralHi := (120481389328711441009/25000000000000000000)
  directionLo := (48450962708416626281/10000000000000000000)
  directionHi := (484509627084166262811/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree095.table
  base := (19310245192448656989027956153218446016033/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-2221503000669281034270290854548171054000000000000)
      constant := (56354877630766107144119522682146409089598836513555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree095.table
  base := (96551225830804618224137976842917395056559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-247114130413005455391656387420881506000000000000)
      constant := (6275408592734433740391024202467772023340092127217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48450962708416626281/10000000000000000000)
  centralHi := (484509627084166262811/100000000000000000000)
  directionLo := (97415997594081235567/20000000000000000000)
  directionHi := (121769996992601544459/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree096.table
  base := (49762193893076431726700958477004574972039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-249430701298529016396700339451170206000000000000)
      constant := (6396152936372469949885457753761339171853641764914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree096.table
  base := (49762193836946785018065178565239624317509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2440070000000000000000000000000000000000000000
      center := (20008574)
      previous := (10004287)
      next := (10004287)
      square := (279755132171347097973651545075900000000000000)
      linear := (-27746013024409102428540868996201134000000000000)
      constant := (712244389424365777235202013584691314021684837126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97415997594081235567/20000000000000000000)
  centralHi := (121769996992601544459/25000000000000000000)
  directionLo := (489636855868983983917/100000000000000000000)
  directionHi := (244818427934491991959/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree097.table
  base := (102539095883923487797030316713659725827017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-2268249622704241260870315255572892654000000000000)
      constant := (58788750818028143992677849577447185954309707906639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree097.table
  base := (102539095788055290187132493754802874357761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (7829442)
      previous := (3914721)
      next := (3914721)
      square := (109469399545309733989689735029700000000000000)
      linear := (-10970178435928625579220837152640822000000000000)
      constant := (284627134145858652407285638713404767246553378041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell102.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489636855868983983917/100000000000000000000)
  centralHi := (244818427934491991959/50000000000000000000)
  directionLo := (492180441067376593817/100000000000000000000)
  directionHi := (246090220533688296909/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree098.table
  base := (52797675115437337386165909988929578943223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 197645670000000000000000000000000000000000000000
      center := (1620694494)
      previous := (810347247)
      next := (810347247)
      square := (22660165705879114935865775151147900000000000000)
      linear := (-2291622933721721374170327456085253454000000000000)
      constant := (60025000802306051411373943953342210834610240358882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree098.table
  base := (52797675074506476734855156223868241757257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21960630000000000000000000000000000000000000000
      center := (180077166)
      previous := (90038583)
      next := (90038583)
      square := (2517796189542123881762863905683100000000000000)
      linear := (-254914090833034854787290688055667606000000000000)
      constant := (6684082334287491333547765611466495263196334158382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell102.Kernel098
