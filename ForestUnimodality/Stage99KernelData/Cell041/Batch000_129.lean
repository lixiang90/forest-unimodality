import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell041.Parameters
import ForestUnimodality.BinomialMassData.Q581_1216.Batch000_049
import ForestUnimodality.BinomialMassData.Q581_1216.Batch050_099
import ForestUnimodality.BinomialMassData.Q581_1216.Batch100_149
import ForestUnimodality.BinomialMassData.Q23_48.Batch000_049
import ForestUnimodality.BinomialMassData.Q23_48.Batch050_099
import ForestUnimodality.BinomialMassData.Q23_48.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree000.table
  base := (2896072678682033293473097063/50000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (23595037369367952151399947500000000000)
      constant := (289607267868203329347309706300000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree000.table
  base := (2896072678682033293473097063/50000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (23595037369367952151399947500000000000)
      constant := (289607267868203329347309706300000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree001.table
  base := (334687721319275039057892598738176019905163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-270238606170827763992142722160000000000000)
      constant := (120882757090633072703342921141520097873263843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree001.table
  base := (166994540853421042754086086706738777496441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-3378897747732992236369131682500000000000)
      constant := (1503709518466856047863245095356117747467969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12487668535430772811/25000000000000000000)
  directionHi := (9990134828344618249/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree002.table
  base := (201172597405156112253160249044523891966759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-557512829322339189437596206415000000000000)
      constant := (72881545541855519238653078394505624999999999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree002.table
  base := (40082594916136152022084012203794254001231/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-13940301663580592084201725785000000000000)
      constant := (1810192991909281742780154718228866430055395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12487668535430772811/25000000000000000000)
  centralHi := (9990134828344618249/20000000000000000000)
  directionLo := (17660230205225963723/25000000000000000000)
  directionHi := (70640920820903854893/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree003.table
  base := (126873031344438614522280223013067992439671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-844787052473850614883049690670000000000000)
      constant := (46394408868000477177998766984899381208221231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree003.table
  base := (2524860983804666659812844835939293473517/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-1173489323983066649759177122500000000000)
      constant := (63948011113620262434226710743013586837925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17660230205225963723/25000000000000000000)
  centralHi := (70640920820903854893/100000000000000000000)
  directionLo := (138427368777250107/160000000000000000)
  directionHi := (21629276371445329219/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree004.table
  base := (21093569131915298838948399120111610460991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-566030637812681020164251587462500000000000)
      constant := (15762311771526199493732657644863864002835502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree004.table
  base := (20974624861797381357850772464622964052717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-14152656999904903653564325312500000000000)
      constant := (390902703273284265188673891573838352948906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138427368777250107/160000000000000000)
  centralHi := (21629276371445329219/25000000000000000000)
  directionLo := (12487668535430772811/12500000000000000000)
  directionHi := (99901348283446182489/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree005.table
  base := (59140414093896986009592134691876965711029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-1419335498776873465773956659180000000000000)
      constant := (23024722858216685050429650562514264309181469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree005.table
  base := (58792246691850142915488769150093491626531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-35487820167924414918592113045000000000000)
      constant := (571132903476200411809031163068028924638779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12487668535430772811/12500000000000000000)
  centralHi := (99901348283446182489/100000000000000000000)
  directionLo := (111693102902833796197/100000000000000000000)
  directionHi := (55846551451416898099/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree006.table
  base := (1736622345715631781333224779250636331119/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-1706609721928384891219410143435000000000000)
      constant := (18094832184001211072817149045299180388348975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree006.table
  base := (43160411512847107532394408300001173567123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-4741147370671002503339508385000000000000)
      constant := (49907975125749740768509676754376173567123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111693102902833796197/100000000000000000000)
  centralHi := (55846551451416898099/50000000000000000000)
  directionLo := (24470732791051128037/20000000000000000000)
  directionHi := (61176831977627820093/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree007.table
  base := (6610062639921153107969947322143313735539/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-1993883945079896316664863627690000000000000)
      constant := (15237019212417672259863298298201767230147895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree007.table
  base := (32859250917596080751304254829911598453901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-49852832504153630141519037885000000000000)
      constant := (378628337579951248922673794007016886085109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24470732791051128037/20000000000000000000)
  centralHi := (61176831977627820093/50000000000000000000)
  directionLo := (132157061599024011997/100000000000000000000)
  directionHi := (66078530799512005999/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree008.table
  base := (25802364890972533132857837546611298638051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-2281158168231407742110317111945000000000000)
      constant := (13641808996288027523006813200586053808336411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree008.table
  base := (6413636057766178580923317934053712171861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-28517669336134118876491250152500000000000)
      constant := (169697300872760011795282969844216819093498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132157061599024011997/100000000000000000000)
  centralHi := (66078530799512005999/50000000000000000000)
  directionLo := (28256368328361541957/20000000000000000000)
  directionHi := (70640920820903854893/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree009.table
  base := (10221799769223711406425793690782847026427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-1284216195691459583777885298100000000000000)
      constant := (6432926158579005183963494925443135120290147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree009.table
  base := (20325077452670489964280688418512808171341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-7135316093375871707160662525000000000000)
      constant := (35608849180356814039192954714450308171341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28256368328361541957/20000000000000000000)
  centralHi := (70640920820903854893/50000000000000000000)
  directionLo := (37463005606292318433/25000000000000000000)
  directionHi := (149852022425169273733/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree010.table
  base := (16288297800358445183641878840016438412491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-2855706614534430593001224080455000000000000)
      constant := (12661604492684032622599560522624059266909251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree010.table
  base := (4047529452531782451117456181082160670513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-35700175504248726487954712572500000000000)
      constant := (157878432631224328195907815429791392069234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37463005606292318433/25000000000000000000)
  centralHi := (149852022425169273733/100000000000000000000)
  directionLo := (39489475237180316623/25000000000000000000)
  directionHi := (157957900948721266493/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree011.table
  base := (1294309347439293674689010464237673396023/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-1571490418842971009223338782355000000000000)
      constant := (6443530161915611382062143993934293448571515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree011.table
  base := (1607451735778970465747206790350648176793/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-39291428588306030293686443782500000000000)
      constant := (160857903454203091321627908999654584364548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39489475237180316623/25000000000000000000)
  centralHi := (157957900948721266493/100000000000000000000)
  directionLo := (165667644153403239789/100000000000000000000)
  directionHi := (16566764415340323979/10000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree012.table
  base := (5087037251546681332938091526502305362871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-1715127530418726721946065524482500000000000)
      constant := (6728888778928705358222611370026550985996431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree012.table
  base := (2525436958399326620276143341674173183531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-4764742408040370455490908332500000000000)
      constant := (18681672607477785437653373290223346367062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165667644153403239789/100000000000000000000)
  centralHi := (16566764415340323979/10000000000000000000)
  directionLo := (173034210971562633751/100000000000000000000)
  directionHi := (21629276371445329219/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree013.table
  base := (7835820446961776400518988227682583698223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-3717529283988964869337584533220000000000000)
      constant := (14321259416103837778593078349415092402558503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree013.table
  base := (1943094587877994083092038766188924178209/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-46473934756420637905149906202500000000000)
      constant := (179061246817312243228994246706244385207762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173034210971562633751/100000000000000000000)
  centralHi := (21629276371445329219/12500000000000000000)
  directionLo := (90049858430987900159/50000000000000000000)
  directionHi := (180099716861975800319/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree014.table
  base := (5833242880217788434384706177094164102423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-4004803507140476294783038017475000000000000)
      constant := (15443178976863783335135247965811305740974703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree014.table
  base := (2888590531570437800128632786447666573509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-50065187840477941710881637412500000000000)
      constant := (193212023808482574634169467983966499161581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90049858430987900159/50000000000000000000)
  centralHi := (180099716861975800319/100000000000000000000)
  directionLo := (186898308876716309077/100000000000000000000)
  directionHi := (93449154438358154539/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree015.table
  base := (4100845773509699432570705892702261917579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-4292077730291987720228491501730000000000000)
      constant := (16799892173541283926171881795159852489746019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree015.table
  base := (4051110920467831965036073969622825809177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-11923653538785610114802970805000000000000)
      constant := (46732151494386286159021063177435325809177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186898308876716309077/100000000000000000000)
  centralHi := (93449154438358154539/50000000000000000000)
  directionLo := (309533006532363183/160000000000000000)
  directionHi := (3022783266917609209/1562500000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree016.table
  base := (2591275419393252056542490181669783257441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-4579351953443499145673944985985000000000000)
      constant := (18374304317748962652492026350846541755936201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree016.table
  base := (2547080619540006272156992634042218531371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-114495388017185098644690199665000000000000)
      constant := (460194655396583212555612102711379966782339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309533006532363183/160000000000000000)
  centralHi := (3022783266917609209/1562500000000000000)
  directionLo := (199802696566892364977/100000000000000000000)
  directionHi := (99901348283446182489/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree017.table
  base := (1268855879834007549694883813250341899093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-4866626176595010571119398470240000000000000)
      constant := (20153536395856387122961213374571928113072573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree017.table
  base := (614787270789087699952689288154395230601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-60838947092649853128076831042500000000000)
      constant := (252460141444636026273087375701358307075409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199802696566892364977/100000000000000000000)
  centralHi := (99901348283446182489/50000000000000000000)
  directionLo := (51487976389283271389/25000000000000000000)
  directionHi := (205951905557133085557/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree018.table
  base := (105825928244105879052076942070083962141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-5153900399746521996564851954495000000000000)
      constant := (22127566605065339865675175512156050310332901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree018.table
  base := (35466069060606521984525232014905813407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-7158911130745239659312062472500000000000)
      constant := (30806516721744053259114882371077405813407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51487976389283271389/25000000000000000000)
  centralHi := (205951905557133085557/100000000000000000000)
  directionLo := (105961381231355782339/50000000000000000000)
  directionHi := (211922762462711564679/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree019.table
  base := (-459969592288615157359294778183183056789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-7536252940301985349044744375000000000000)
      constant := (33640454170241468495726901412266035693211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree019.table
  base := (-950903588938450886287238209853723192993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-136042906521528921479080586925000000000000)
      constant := (608787196719977800093574277977878991263063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105961381231355782339/50000000000000000000)
  centralHi := (211922762462711564679/100000000000000000000)
  directionLo := (27216242593187652881/12500000000000000000)
  directionHi := (217729940745501223049/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree020.table
  base := (-456593251369533794418506363868920773203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-2864224423024772423727879461502500000000000)
      constant := (13314793151495605930476805434434295451747434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree020.table
  base := (-74152656654560772573865519850065819819/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-143225412689643529090544049345000000000000)
      constant := (667569016084157750523345582339985190540725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27216242593187652881/12500000000000000000)
  centralHi := (217729940745501223049/100000000000000000000)
  directionLo := (44677241161133518479/20000000000000000000)
  directionHi := (55846551451416898099/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree021.table
  base := (-525636502738609142177666980129513158291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-6015723069201056272901212407260000000000000)
      constant := (29145792561792322929403788063307908436784745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree021.table
  base := (-2652473418949254010813484014223925306121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-16711990984195348522445279085000000000000)
      constant := (81192306156754328224215864410463574693879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44677241161133518479/20000000000000000000)
  centralHi := (55846551451416898099/25000000000000000000)
  directionLo := (45780549053703880383/20000000000000000000)
  directionHi := (57225686317129850479/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree022.table
  base := (-1668762509581226938664472175377924515619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-3151498646176283849173332945757500000000000)
      constant := (15916318949214577930317056725660287999861541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree022.table
  base := (-335899761380129466872402337098593779851/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-78795212512936372156735487092500000000000)
      constant := (399081653772953576670019823037750779906705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45780549053703880383/20000000000000000000)
  centralHi := (57225686317129850479/25000000000000000000)
  directionLo := (46857885841628529589/20000000000000000000)
  directionHi := (117144714604071323973/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree023.table
  base := (-3964504940830372422517121885392487198273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-6590271515504079123792119375770000000000000)
      constant := (34686474617662922053511409256173898058923447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree023.table
  base := (-3983462605494781821417283977257628288367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-164772931193987351924934436605000000000000)
      constant := (869776010048340583689584930287493845404697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46857885841628529589/20000000000000000000)
  centralHi := (117144714604071323973/50000000000000000000)
  directionLo := (119777508829798561223/50000000000000000000)
  directionHi := (239555017659597122447/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree024.table
  base := (-4517552087006609095656061738144257767607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-6877545738655590549237572860025000000000000)
      constant := (37704259558693780910573322359543047945893873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree024.table
  base := (-2267134929049711749706582495094253962921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-9553079853450108863133216612500000000000)
      constant := (52527402763414548488438863328655746037079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119777508829798561223/50000000000000000000)
  centralHi := (239555017659597122447/100000000000000000000)
  directionLo := (24470732791051128037/10000000000000000000)
  directionHi := (244707327910511280371/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree025.table
  base := (-1250929490005134398386615222870914448941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-3582409980903550987341513172140000000000000)
      constant := (20441723564590414263637400575377727111614598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree025.table
  base := (-627305570022134473963183616386775434889/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-89568971765108283573930680722500000000000)
      constant := (512625899964107157923019626134294834343996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24470732791051128037/10000000000000000000)
  centralHi := (244707327910511280371/100000000000000000000)
  directionLo := (249753370708615456221/100000000000000000000)
  directionHi := (124876685354307728111/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree026.table
  base := (-169653521005425508678228450871934398177/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-3726047092479306700064239914267500000000000)
      constant := (22110951889291619217554466924515894416129648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree026.table
  base := (-1088374473619198449001732718145550427143/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-186320449698331174759324823865000000000000)
      constant := (1108998689701283630931573857229075230778565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249753370708615456221/100000000000000000000)
  centralHi := (124876685354307728111/50000000000000000000)
  directionLo := (127349731082880285789/50000000000000000000)
  directionHi := (254699462165760571579/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree027.table
  base := (-5798097134214929156414229216913836165013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-7739368408110124825573933312790000000000000)
      constant := (47717838618120591307083890042477191081930307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree027.table
  base := (-2904745765662209737710528341777018607101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-10750164214802543465043793682500000000000)
      constant := (66482748600858644361312143631504231392899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127349731082880285789/50000000000000000000)
  centralHi := (254699462165760571579/100000000000000000000)
  directionLo := (259551316457343950627/100000000000000000000)
  directionHi := (64887829114335987657/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree028.table
  base := (-6115440521825438842655589463745982089989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-8026642631261636251019386797045000000000000)
      constant := (51369746575372059639915199365004887965513971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree028.table
  base := (-191420322729802005592299591379248608263/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-100342731017280194991125874352500000000000)
      constant := (644143410386654229149037494125763200410128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259551316457343950627/100000000000000000000)
  centralHi := (64887829114335987657/25000000000000000000)
  directionLo := (132157061599024011997/50000000000000000000)
  directionHi := (52862824639609604799/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree029.table
  base := (-6384450177738900104842603999652388860221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-8313916854413147676464840281300000000000000)
      constant := (55176361499610757962204969984532167308960219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree029.table
  base := (-799154616115166949308435941621806466211/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-103933984101337498796857605562500000000000)
      constant := (691879667010101863582595983448958717216404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132157061599024011997/50000000000000000000)
  centralHi := (52862824639609604799/20000000000000000000)
  directionLo := (268992612480650688343/100000000000000000000)
  directionHi := (33624076560081336043/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree030.table
  base := (-6608079281439733104707860513588511245881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-8601191077564659101910293765555000000000000)
      constant := (59136617293042810595567737745346109940236959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree030.table
  base := (-3307893511350865339945419166322364819407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-11947248576154978066954370752500000000000)
      constant := (82393366298670707360200933494615135180593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268992612480650688343/100000000000000000000)
  centralHi := (33624076560081336043/12500000000000000000)
  directionLo := (273591109900117398429/100000000000000000000)
  directionHi := (27359110990011739843/10000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree031.table
  base := (-3394408194192120896368465189904519037713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-4444232650358085263677873624905000000000000)
      constant := (31624807793574245906939105690670386596135607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree031.table
  base := (-271822931177904241094724375293929865177/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-222232980538904212816642135965000000000000)
      constant := (1586228344804140664924049265734178280335175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273591109900117398429/100000000000000000000)
  centralHi := (27359110990011739843/10000000000000000000)
  directionLo := (8691049480800653727/3125000000000000000)
  directionHi := (55622716677124183853/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree032.table
  base := (-6928760071475609964616194293938663706503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-9175739523867681952801200734065000000000000)
      constant := (67514598797109752266893607461395642401952417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree032.table
  base := (-138693598221640909818525455401364971733/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-114707743353509410214052799192500000000000)
      constant := (846591915198549884900123303299692881360075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8691049480800653727/3125000000000000000)
  centralHi := (55622716677124183853/20000000000000000000)
  directionLo := (282563683283615419571/100000000000000000000)
  directionHi := (70640920820903854893/25000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree033.table
  base := (-7029681256956818011679118868376944595339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-9463013747019193378246654218320000000000000)
      constant := (71930927618552876033342544538434477688582621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree033.table
  base := (-7034864911275123336336652829948680397009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-26288665875014825337729895645000000000000)
      constant := (200436803134657708746696322943488819602991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282563683283615419571/100000000000000000000)
  centralHi := (70640920820903854893/25000000000000000000)
  directionLo := (2241756069093245893/781250000000000000)
  directionHi := (57388955368787094861/20000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree034.table
  base := (-709307535851035193935800629642176694431/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-4875143985085352401846053851287500000000000)
      constant := (38249031103569242832631980760338371066552045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree034.table
  base := (-1774403021938304556617537646599622653623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-121890249521624017825516261612500000000000)
      constant := (959228591989531041859136028095269292234786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2241756069093245893/781250000000000000)
  centralHi := (57388955368787094861/20000000000000000000)
  directionLo := (145629989017740205843/50000000000000000000)
  directionHi := (291259978035480411687/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree035.table
  base := (-7120205931275996892479493442460862649221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-10037562193322216229137561186830000000000000)
      constant := (81215546419461118725375442500078464521131219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree035.table
  base := (-3562087305972731424481137324298170298727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-125481502605681321631247992822500000000000)
      constant := (1018375209577832845302771239107097717311457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145629989017740205843/50000000000000000000)
  centralHi := (291259978035480411687/100000000000000000000)
  directionLo := (9234755420063898293/3125000000000000000)
  directionHi := (295512173442044745377/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree036.table
  base := (-284485650517477554313003295495901766741/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-10324836416473727654583014671085000000000000)
      constant := (86082994603667145072448865225433549055162475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree036.table
  base := (-3557805753115772060267030499202510854051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-14341417298859847270775524892500000000000)
      constant := (119933411252239612062866047151422489145949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9234755420063898293/3125000000000000000)
  centralHi := (295512173442044745377/100000000000000000000)
  directionLo := (59940808970067709493/20000000000000000000)
  directionHi := (149852022425169273733/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree037.table
  base := (-7069785073038681612308369391754073097709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-10612110639625239080028468155340000000000000)
      constant := (91100080517000637843018421446693459299227051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree037.table
  base := (-884102280286185747033430072424236489593/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-132664008773795929242711455242500000000000)
      constant := (1142301037443950923940336894616321236374652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59940808970067709493/20000000000000000000)
  centralHi := (149852022425169273733/50000000000000000000)
  directionLo := (75959522258102350891/25000000000000000000)
  directionHi := (60767617806481880713/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree038.table
  base := (-6993902291212465462123576748131660548443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-30192201835946677300481777395000000000000)
      constant := (266666282603503377525063703369055839451557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree038.table
  base := (-109321131607192768099940460041132263601/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-136255261857853233048443186452500000000000)
      constant := (1207072808886881372086346657637841408082912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75959522258102350891/25000000000000000000)
  centralHi := (60767617806481880713/20000000000000000000)
  directionLo := (30791663513697818299/10000000000000000000)
  directionHi := (307916635136978182991/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree039.table
  base := (-275405628821255071097078965492367147737/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-11186659085928261930919375123850000000000000)
      constant := (101582103255350005223411178279279472429173575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree039.table
  base := (-6887455354234919408194005725311662359571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-31077003320424563745372203925000000000000)
      constant := (283047362160142034481798238180000837640429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30791663513697818299/10000000000000000000)
  centralHi := (307916635136978182991/100000000000000000000)
  directionLo := (311941860033711332049/100000000000000000000)
  directionHi := (6238837200674226641/2000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree040.table
  base := (-3372024628379596892607569770107636262951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-5736966654539886678182414304052500000000000)
      constant := (53523304036042885856831100442364580809074689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree040.table
  base := (-674607018085172032020063452215678846133/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-143437768025967840659906648872500000000000)
      constant := (1342219555795251079010144284206544451924015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311941860033711332049/100000000000000000000)
  centralHi := (6238837200674226641/2000000000000000000)
  directionLo := (63183160379488506597/20000000000000000000)
  directionHi := (157957900948721266493/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree041.table
  base := (-821386652788081904589233617792538219339/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-5880603766115642390905141046180000000000000)
      constant := (56329937244341232034054276190908102155024484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree041.table
  base := (-1643214285276718243535453188282526888963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-147029021110025144465638380082500000000000)
      constant := (1412590016037934544753737478687633265998666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63183160379488506597/20000000000000000000)
  centralHi := (157957900948721266493/50000000000000000000)
  directionLo := (15992018613648869109/5000000000000000000)
  directionHi := (319840372272977382181/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree042.table
  base := (-6366667280970244360944605721504378334211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-12048481755382796207255735576615000000000000)
      constant := (118421760031507385841073491711147544421349829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree042.table
  base := (-6368206410502512154432851562364986040351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-33471172043129432949193358065000000000000)
      constant := (329960612146428876859778390023260013959649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15992018613648869109/5000000000000000000)
  centralHi := (319840372272977382181/100000000000000000000)
  directionLo := (64743473364634790153/20000000000000000000)
  directionHi := (161858683411586975383/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree043.table
  base := (-3065553161323736918752470963410736545347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-6167877989267153816350594530435000000000000)
      constant := (62166071902654850477611144071496517075879733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree043.table
  base := (-1533112230285980159921298024890043695927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-154211527278139752077101842502500000000000)
      constant := (1558916282463763509852188628284010463473314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64743473364634790153/20000000000000000000)
  centralHi := (161858683411586975383/50000000000000000000)
  directionLo := (327548474931790770441/100000000000000000000)
  directionHi := (163774237465895385221/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree044.table
  base := (-5864694643181013317147848736518424706759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-12623030201685819058146642545125000000000000)
      constant := (130390923179289483666633119082012786180860001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree044.table
  base := (-5865865482544124890713578429755397567871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-315605560724394111765667147425000000000000)
      constant := (3269738671619253235259257499865951421889161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327548474931790770441/100000000000000000000)
  centralHi := (163774237465895385221/50000000000000000000)
  directionLo := (165667644153403239789/50000000000000000000)
  directionHi := (331335288306806479579/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree045.table
  base := (-1113534738287674066859516157494024027351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-12910304424837330483592096029380000000000000)
      constant := (136598010990405563755378828604294966318131445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree045.table
  base := (-5568694475430306485862283871099261798289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-35865340765834302153014512205000000000000)
      constant := (380595742662943767133060864471088238201711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165667644153403239789/50000000000000000000)
  centralHi := (331335288306806479579/100000000000000000000)
  directionLo := (20942456794281336787/6250000000000000000)
  directionHi := (335079308708501388593/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree046.table
  base := (-1048049722265449589643418776123140154879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-13197578647988841909037549513635000000000000)
      constant := (142953333181707260417065489665700544520443405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree046.table
  base := (-1310284586476454333422116369066201679269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-164985286530311663494297036132500000000000)
      constant := (1792349889977159429671116842107745869773158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20942456794281336787/6250000000000000000)
  centralHi := (335079308708501388593/100000000000000000000)
  directionLo := (10586936090897766907/3125000000000000000)
  directionHi := (13551278196349141641/4000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree047.table
  base := (-122064844239418851036193105701199745249/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-6742426435570176667241501498945000000000000)
      constant := (74728413403402682853047839946832005808052220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree047.table
  base := (-4883369090373739914945075275564799414869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-337153079228737934600057534685000000000000)
      constant := (3747751411615100358366538643520229305266179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10586936090897766907/3125000000000000000)
  centralHi := (13551278196349141641/4000000000000000000)
  directionLo := (5350696390200584169/1562500000000000000)
  directionHi := (342444568972837386817/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree048.table
  base := (-2247428714643625645735781707691268289347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-6886063547145932379964228241072500000000000)
      constant := (78054219171360324347949182112889077147545733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree048.table
  base := (-899106578162406630634879609873474021387/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-38259509488539171356835666345000000000000)
      constant := (434946140367892974550953566125632629893065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5350696390200584169/1562500000000000000)
  centralHi := (342444568972837386817/100000000000000000000)
  directionLo := (346068421943125267503/100000000000000000000)
  directionHi := (21629276371445329219/6250000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree049.table
  base := (-2038582851760870254272936291142839204071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-7029700658721688092686954983200000000000000)
      constant := (81454061131318683046985335695311712391080369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree049.table
  base := (-4077754034266105935111401726766783545893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-351518091564967149822984459525000000000000)
      constant := (4084990216458719417137749327685036448086963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346068421943125267503/100000000000000000000)
  centralHi := (21629276371445329219/6250000000000000000)
  directionLo := (349654718992061638709/100000000000000000000)
  directionHi := (34965471899206163871/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree050.table
  base := (-3629625901703624579322513368770765849519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-14346675540594887610819363450655000000000000)
      constant := (169855839827853669458231279336155003528323641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree050.table
  base := (-226883639308286858943429635427154908211/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-179350298866540878717223960972500000000000)
      constant := (2129587659842189306781495625225807346608808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349654718992061638709/100000000000000000000)
  centralHi := (34965471899206163871/10000000000000000000)
  directionLo := (11037643878266227327/3125000000000000000)
  directionHi := (70640920820903854893/20000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree051.table
  base := (-3152329363593286891547092136905150027623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-14633949763746399036264816934910000000000000)
      constant := (176951558064716060385704024165666576777528097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree051.table
  base := (-1576387705618481314006058148464245519043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-20326839105622020280328410242500000000000)
      constant := (246503875753343614320906786393567004480957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11037643878266227327/3125000000000000000)
  centralHi := (70640920820903854893/20000000000000000000)
  directionLo := (356719164340581508073/100000000000000000000)
  directionHi := (178359582170290754037/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree052.table
  base := (-1322676930276142223431296636365175058811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-7460611993448955230855135209582500000000000)
      constant := (92097624448881508399397894257898578053769229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree052.table
  base := (-661435530817115572582806395390882782069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-186532805034655486328687423392500000000000)
      constant := (2309336429603667805236764582201089109922758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356719164340581508073/100000000000000000000)
  centralHi := (178359582170290754037/50000000000000000000)
  directionLo := (360199433723951600637/100000000000000000000)
  directionHi := (180099716861975800319/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree053.table
  base := (-131797851948895409725939167829974658047/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-7604249105024710943577861951710000000000000)
      constant := (95793444207429660818235831404692873031310264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree053.table
  base := (-421820705468007556520027122344647170759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-380248116237425580268838309205000000000000)
      constant := (4803984020165013730181680876086678377315845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360199433723951600637/100000000000000000000)
  centralHi := (180099716861975800319/50000000000000000000)
  directionLo := (363646396795386940817/100000000000000000000)
  directionHi := (181823198397693470409/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree054.table
  base := (-771310553921219924039653668446336663109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-7747886216600466656300588693837500000000000)
      constant := (99563228121961683142601201372513841214617651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree054.table
  base := (-77145755694181606410498239567058396611/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-21523923466974454882238987312500000000000)
      constant := (277389041501073996093903179139016916033890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363646396795386940817/100000000000000000000)
  centralHi := (181823198397693470409/50000000000000000000)
  directionLo := (91765247966441730139/25000000000000000000)
  directionHi := (367060991865766920557/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree055.table
  base := (-473484190832982845722232037816786164677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-7891523328176222369023315435965000000000000)
      constant := (103406967512028007255716384454285933163301603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree055.table
  base := (-473612075017606562213578729557787636647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-197306564286827397745882617022500000000000)
      constant := (2592864307183033249411930105300386161270177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91765247966441730139/25000000000000000000)
  centralHi := (367060991865766920557/100000000000000000000)
  directionLo := (370444113999255241637/100000000000000000000)
  directionHi := (185222056999627620819/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree056.table
  base := (-321848446239967974207697778686162097731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-16070320879503956163492084356185000000000000)
      constant := (214649309956572336251415271783354920482719109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree056.table
  base := (-161035454414901276904754826132159868631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-200897817370884701551614348232500000000000)
      constant := (2691080629873951120769734835023560561182321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370444113999255241637/100000000000000000000)
  centralHi := (185222056999627620819/50000000000000000000)
  directionLo := (186898308876716309077/50000000000000000000)
  directionHi := (74759323550686523631/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree057.table
  base := (332703746159275709225733604292995773459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-45311897791289383902874066040000000000000)
      constant := (616710715855126302752270396813160183273459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree057.table
  base := (332510287318579353555182219038006584331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-45442015656653778968299128765000000000000)
      constant := (620255597140345886196255048349975506584331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186898308876716309077/50000000000000000000)
  centralHi := (74759323550686523631/20000000000000000000)
  directionLo := (377119319700169194411/100000000000000000000)
  directionHi := (94279829925042298603/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree058.table
  base := (508329193576746073358026008792126650303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-8322434662903489507191495662347500000000000)
      constant := (115381849832308117504156666714522395220759383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree058.table
  base := (1016490180427568587988881201318649952451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-416160647077998618326155621305000000000000)
      constant := (5786145694589857425417235173327492849572059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377119319700169194411/100000000000000000000)
  centralHi := (94279829925042298603/25000000000000000000)
  directionLo := (380413000748306477921/100000000000000000000)
  directionHi := (190206500374153238961/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree059.table
  base := (864995024744346276625242581333273394899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-8466071774479245219914222404475000000000000)
      constant := (119521347250040282722128410761035354664308539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree059.table
  base := (216230478005048886322553576533731433843/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-211671576623056612968809541862500000000000)
      constant := (2996848498105012311981044228219745581618348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380413000748306477921/100000000000000000000)
  centralHi := (190206500374153238961/50000000000000000000)
  directionLo := (383678408286866761507/100000000000000000000)
  directionHi := (95919602071716690377/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree060.table
  base := (1236338519227162529290574252287109941331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-8609708886055000932636949146602500000000000)
      constant := (123734772549151538688120295605752990438820491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree060.table
  base := (98901997732579475409847794301657962681/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-47836184379358648172120282905000000000000)
      constant := (689439343072225725735122513126291449067025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383678408286866761507/100000000000000000000)
  centralHi := (95919602071716690377/25000000000000000000)
  directionLo := (386916258165453978751/100000000000000000000)
  directionHi := (3022783266917609209/781250000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree061.table
  base := (3244700840199054620746199921940340520343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-17506691995261513290719351777460000000000000)
      constant := (256044244775783438854116417491537142615343823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree061.table
  base := (3244590390949097704950239043447900067933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-437708165582342441160546008565000000000000)
      constant := (6419916805584171323975954190375718600611397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386916258165453978751/100000000000000000000)
  centralHi := (3022783266917609209/781250000000000000)
  directionLo := (39012723652671167553/10000000000000000000)
  directionHi := (390127236526711675531/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree062.table
  base := (4046045652303468081546962538767941888627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-17793966218413024716164805261715000000000000)
      constant := (264766787827848241727774578009929289521794347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree062.table
  base := (252871855277320929133515312545695388819/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-222445335875228524386004735492500000000000)
      constant := (3319292505334940101444818163816727567994968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39012723652671167553/10000000000000000000)
  centralHi := (390127236526711675531/100000000000000000000)
  directionLo := (19665600075206289039/5000000000000000000)
  directionHi := (393312001504125780781/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree063.table
  base := (4876697984211872926420760262024022917001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-18081240441564536141610258745970000000000000)
      constant := (273637169384406880999457946697097508210537361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree063.table
  base := (4876614612354516642190880128869897272817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-50230353102063517375941437045000000000000)
      constant := (762328731556037936979736559611682397272817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19665600075206289039/5000000000000000000)
  centralHi := (393312001504125780781/100000000000000000000)
  directionLo := (396471184797072035991/100000000000000000000)
  directionHi := (49558898099634004499/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree064.table
  base := (1434161579254617978052697575255628721077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-9184257332358023783527856115112500000000000)
      constant := (141327692643567181932193458872802063936617594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree064.table
  base := (573657389928068373185430582195253638253/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-229627842043343131997468197912500000000000)
      constant := (3543518712054384990024296884768786413721385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396471184797072035991/100000000000000000000)
  centralHi := (49558898099634004499/12500000000000000000)
  directionLo := (199802696566892364977/50000000000000000000)
  directionHi := (79921078626756945991/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree065.table
  base := (414117550856423805752737329092561450977/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-9327894443933779496250582857240000000000000)
      constant := (145910715992433147772770122979778594814171576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree065.table
  base := (6625817920532292888636294838715418279189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-466438190254800871606399858245000000000000)
      constant := (7316821444361015755364118481559376264512701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199802696566892364977/50000000000000000000)
  centralHi := (79921078626756945991/20000000000000000000)
  directionLo := (80543041926368599771/20000000000000000000)
  directionHi := (50339401203980374857/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree066.table
  base := (1886098268065381283809922329482940753007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-9471531555509535208973309599367500000000000)
      constant := (150567653222239746932571209092815433223671054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree066.table
  base := (7544338459234358026188116128539000879607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-52624521824768386579762591185000000000000)
      constant := (838923396756578209331896065901664000879607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80543041926368599771/20000000000000000000)
  centralHi := (50339401203980374857/12500000000000000000)
  directionLo := (202900597532407390367/50000000000000000000)
  directionHi := (81160239012962956147/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree067.table
  base := (4246087957664131728113606996749217611011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-9615168667085290921696036341495000000000000)
      constant := (155298503037472336777601106142002385526324971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree067.table
  base := (4246064249694057076437032681983288050521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-240401601295515043414663391542500000000000)
      constant := (3893752370154672740496355382628630842454689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202900597532407390367/50000000000000000000)
  centralHi := (81160239012962956147/20000000000000000000)
  directionLo := (81772777808570123157/20000000000000000000)
  directionHi := (204431944521425307893/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree068.table
  base := (118365290135503589200633864069040807633/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-9758805778661046634418763083622500000000000)
      constant := (160103264331293598384088317106257730512220520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree068.table
  base := (9469182049555159351907771660643197225183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-487985708759144694440790245505000000000000)
      constant := (8028403898938494929129979660027038775026647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81772777808570123157/20000000000000000000)
  centralHi := (204431944521425307893/50000000000000000000)
  directionLo := (51487976389283271389/12500000000000000000)
  directionHi := (411903811114266171113/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree069.table
  base := (20951059438264702949239756466217499339/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-9902442890236802347141489825750000000000000)
      constant := (164981936157943955083666543470779469159094750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree069.table
  base := (327359187268447432309552877304964750277/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-27509345273736627891791872662500000000000)
      constant := (459611555591241424794134410606723186004432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51487976389283271389/12500000000000000000)
  centralHi := (411903811114266171113/100000000000000000000)
  directionLo := (16596858471779274293/4000000000000000000)
  directionHi := (207460730897240928663/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree070.table
  base := (5755545481265795544105179301016406807077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-10046080001812558059864216567877500000000000)
      constant := (169934517709203454674573537765650516607354797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree070.table
  base := (11511059957544142735587277874394670687183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-502350721095373909663717170345000000000000)
      constant := (8521317006082352610716505019378927036184647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16596858471779274293/4000000000000000000)
  centralHi := (207460730897240928663/50000000000000000000)
  directionLo := (417917323528090028693/100000000000000000000)
  directionHi := (208958661764045014347/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree071.table
  base := (6287951557058480807181227507123196606737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-10189717113388313772586943310005000000000000)
      constant := (174961008294312848649385325004013016943782057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree071.table
  base := (6287938105219686923045414869823617769059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-254766613631744258637590316382500000000000)
      constant := (4386665440826360240249240625747318809921531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417917323528090028693/100000000000000000000)
  centralHi := (208958661764045014347/50000000000000000000)
  directionLo := (420891861589286227607/100000000000000000000)
  directionHi := (52611482698660778451/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree072.table
  base := (3417490725701523173307649817553984356501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-10333354224964069485309670052132500000000000)
      constant := (180061407322841769158149780125851164205393722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree072.table
  base := (13669939561120259044702640429225980435503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-57412859270178124987404899465000000000000)
      constant := (1003227733182449720728213858011725980435503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420891861589286227607/100000000000000000000)
  centralHi := (52611482698660778451/12500000000000000000)
  directionLo := (105961381231355782339/25000000000000000000)
  directionHi := (423845524925423129357/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree073.table
  base := (14793267532356311591410345596398868244157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-20953982673079650396064793588520000000000000)
      constant := (370471428580136827544974801338081046123640677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree073.table
  base := (3698311820948287751429574658682562112153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-261949119799858866249053778802500000000000)
      constant := (4644236566259095401475747864718004868018754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105961381231355782339/25000000000000000000)
  centralHi := (423845524925423129357/100000000000000000000)
  directionLo := (5334734336850220603/1250000000000000000)
  directionHi := (426778746948017648241/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree074.table
  base := (7972907306113213166717151045995381268491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-10620628448115580910755123536387500000000000)
      constant := (190483928764500097340826322395485895137925251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree074.table
  base := (15945797049232762200068438401615236420851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-531080745767832340109571020025000000000000)
      constant := (9551601462318122841929569979895162127787659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5334734336850220603/1250000000000000000)
  centralHi := (426778746948017648241/100000000000000000000)
  directionLo := (53711493284394665339/12500000000000000000)
  directionHi := (429691946275157322713/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree075.table
  base := (17127602098551450022277651005379053118517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-21528531119382673246955700557030000000000000)
      constant := (391612100754438379456507131402042424113284637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree075.table
  base := (267618544795791446723600617605087296819/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-29903513996441497095613026802500000000000)
      constant := (545468587229292646841731327314144043498208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53711493284394665339/12500000000000000000)
  centralHi := (429691946275157322713/100000000000000000000)
  directionLo := (432585527428906584379/100000000000000000000)
  directionHi := (21629276371445329219/5000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree076.table
  base := (2292328530467760814692836721701050876991/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-30215796873316045252633177342500000000000)
      constant := (557346478705777902995643617714772953507964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree076.table
  base := (9169307517859583291466688353440942385479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-272722879052030777666248972432500000000000)
      constant := (5044486220317558153137339568492843481469311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432585527428906584379/100000000000000000000)
  centralHi := (21629276371445329219/5000000000000000000)
  directionLo := (27216242593187652881/6250000000000000000)
  directionHi := (435459881491002446097/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree077.table
  base := (4894722888360369966009733171870407647899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-11051539782842848048923303762770000000000000)
      constant := (206672013801468584600435778441011274165533078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree077.table
  base := (19578880101622080655190725803804722117709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-552628264272176162943961407285000000000000)
      constant := (10363215060755882819595396998643929999059381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27216242593187652881/6250000000000000000)
  centralHi := (435459881491002446097/100000000000000000000)
  directionLo := (438315386719848677747/100000000000000000000)
  directionHi := (109578846679962169437/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree078.table
  base := (20848390749759372247455063464231931727669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-22390353788837207523292061009795000000000000)
      constant := (424431710225216566099591345231833039853688509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree078.table
  base := (20848380821868545702405456112267563197559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-62201196715587863395047207745000000000000)
      constant := (1182351379922736615685691577809142563197559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438315386719848677747/100000000000000000000)
  centralHi := (109578846679962169437/25000000000000000000)
  directionLo := (44115240913156430647/10000000000000000000)
  directionHi := (441152409131564306471/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree079.table
  base := (11073562369931711315600438906797669808029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-11338814005994359474368757247025000000000000)
      constant := (217833602548948680772402495923356126769448469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree079.table
  base := (5536779033541119121277262194421150025633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-283496638304202689083444166062500000000000)
      constant := (5461407253360354851923472036104736950461394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44115240913156430647/10000000000000000000)
  centralHi := (441152409131564306471/100000000000000000000)
  directionLo := (443971303047613322171/100000000000000000000)
  directionHi := (110992825761903330543/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree080.table
  base := (23475092589143246651599990501924907558073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-22964902235140230374182967978305000000000000)
      constant := (447050511883585206781225321657313641628464353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree080.table
  base := (23475085130449557767488411297443752314517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-574175782776519985778351794545000000000000)
      constant := (11208171314831580470500238781901993770830653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443971303047613322171/100000000000000000000)
  centralHi := (110992825761903330543/25000000000000000000)
  directionLo := (44677241161133518479/10000000000000000000)
  directionHi := (446772411611335184791/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree081.table
  base := (24832293498278335106623585678044921625213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-23252176458291741799628421462560000000000000)
      constant := (458581630293725397986919932141362771394201893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree081.table
  base := (24832287034482060882501905303376879808971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-64595365438292732598868361885000000000000)
      constant := (1277470315183451809236414842671814379808971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44677241161133518479/10000000000000000000)
  centralHi := (446772411611335184791/100000000000000000000)
  directionLo := (224778033637753910599/50000000000000000000)
  directionHi := (449556067275507821199/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree082.table
  base := (13109363391819716465010983617115589120709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-11769725340721626612536937473407500000000000)
      constant := (235130280040763887041486341501985602672575949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree082.table
  base := (6554680295672677261112326434819353460863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-294270397556374600500639359692500000000000)
      constant := (5894999533103512825329063226568310862295534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224778033637753910599/50000000000000000000)
  centralHi := (449556067275507821199/100000000000000000000)
  directionLo := (4523225922629042393/1000000000000000000)
  directionHi := (452322592262904239301/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree083.table
  base := (13817195930268394743712823564728501900143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-11913362452297382325259664215535000000000000)
      constant := (241043650517959667545188094531164157154701623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree083.table
  base := (3454298375976931042483674455956213321423/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-297861650640431904306371090902500000000000)
      constant := (6043234999197059043935133218277704929571228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4523225922629042393/1000000000000000000)
  centralHi := (452322592262904239301/100000000000000000000)
  directionLo := (227536149500824440911/50000000000000000000)
  directionHi := (455072299001648881823/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree084.table
  base := (14539644114450054812453446665107977475989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-12056999563873138037982390957662500000000000)
      constant := (247030926488187352229281269526169136118832029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree084.table
  base := (14539642012464669428538317605128251768769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-33494767080498800901344758012500000000000)
      constant := (688146979380444507531054648663253251768769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227536149500824440911/50000000000000000000)
  centralHi := (455072299001648881823/100000000000000000000)
  directionLo := (45780549053703880383/10000000000000000000)
  directionHi := (457805490537038803831/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree085.table
  base := (7638353865258974343470865708553582313087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-12200636675448893750705117699790000000000000)
      constant := (253092107874248265071436771625086526273798814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree085.table
  base := (611068236389874261707297305699146767507/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-305044156808546511917834553322500000000000)
      constant := (6345262976918913393063961369503401772689075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45780549053703880383/10000000000000000000)
  centralHi := (457805490537038803831/100000000000000000000)
  directionLo := (115130615230341569223/25000000000000000000)
  directionHi := (460522460921366276893/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree086.table
  base := (6411354638231952923860103458072083907271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-24688547574049298926855688883835000000000000)
      constant := (518454389220236648033774405011088548952624155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree086.table
  base := (8014192509287453667679577520518681121913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-308635409892603815723566284532500000000000)
      constant := (6499055485087183116195470821826523760194434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115130615230341569223/25000000000000000000)
  centralHi := (460522460921366276893/100000000000000000000)
  directionLo := (57902936947895280843/12500000000000000000)
  directionHi := (92644699116632449349/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree087.table
  base := (33589361106445512152772114070745797367113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-24975821797200810352301142368090000000000000)
      constant := (530872373278664800217037799046409818787027793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree087.table
  base := (6717871674998730520297911691339768036717/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-69383702883702471006510670165000000000000)
      constant := (1478822297236831506138134854397011340183585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57902936947895280843/12500000000000000000)
  centralHi := (92644699116632449349/20000000000000000000)
  directionLo := (465908871677173085997/100000000000000000000)
  directionHi := (232954435838586542999/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree088.table
  base := (17575589469685258053925035112612710336087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-12631548010176160888873297926172500000000000)
      constant := (271719083913602659738437965655567250931327407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree088.table
  base := (17575588287058953644309110950189986509103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-315817916060718423335029746952500000000000)
      constant := (6812197533189506439191597690095459878581927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465908871677173085997/100000000000000000000)
  centralHi := (232954435838586542999/50000000000000000000)
  directionLo := (46857885841628529589/10000000000000000000)
  directionHi := (468578858416285295891/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree089.table
  base := (3674222646116913414286621335644263492879/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-12775185121751916601596024668300000000000000)
      constant := (278075886391636904463973295784908422948396595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree089.table
  base := (7348444882647272046060721283148579056869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-638818338289551454281522956325000000000000)
      constant := (13943094141925378235294680469530123557559105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46857885841628529589/10000000000000000000)
  centralHi := (468578858416285295891/100000000000000000000)
  directionLo := (471233717386523335301/100000000000000000000)
  directionHi := (235616858693261667651/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree090.table
  base := (9590625869058325924104450813042791996863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-12918822233327672314318751410427500000000000)
      constant := (284506594038127878992791695302921583321735086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree090.table
  base := (38362501703233299211509145881194252528841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-71777871606407340210331824305000000000000)
      constant := (1585055322229837579560259984721819252528841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471233717386523335301/100000000000000000000)
  centralHi := (235616858693261667651/50000000000000000000)
  directionLo := (236936851423081899739/50000000000000000000)
  directionHi := (473873702846163799479/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree091.table
  base := (20006004908661468675854996754019462067741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-13062459344903428027041478152555000000000000)
      constant := (291011206822888747546161694433617568775204501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree091.table
  base := (40012008282503366000954390158147100842789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-653183350625780669504449881165000000000000)
      constant := (14591606339354044596544649507842386407585101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236936851423081899739/50000000000000000000)
  centralHi := (473873702846163799479/100000000000000000000)
  directionLo := (119124765502483506701/25000000000000000000)
  directionHi := (95299812401986805361/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree092.table
  base := (41690745341468721862035291555944830402651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-26412192912958367479528409789365000000000000)
      constant := (595179449440227098166105181536908271275357011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree092.table
  base := (10422686003241737475551277201880309582009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-330182928396947638557956671792500000000000)
      constant := (7460709729269590440266850665808220572476162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119124765502483506701/25000000000000000000)
  centralHi := (95299812401986805361/20000000000000000000)
  directionLo := (119777508829798561223/25000000000000000000)
  directionHi := (479110035319194244893/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree093.table
  base := (43398709926467003350519200738549880885471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-26699467136109878904973863273620000000000000)
      constant := (608484295415489048157377075321563186687155031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree093.table
  base := (43398708776662987407895495151276467378687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-74172040329112209414152978445000000000000)
      constant := (1694993028506921944049244785968463967378687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119777508829798561223/25000000000000000000)
  centralHi := (479110035319194244893/100000000000000000000)
  directionLo := (240853428349469504009/50000000000000000000)
  directionHi := (481706856698939008019/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree094.table
  base := (4513590346788102212571925815364270955233/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-13493370679630695165209658378937500000000000)
      constant := (310968475766930837408764170556750790324195565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree094.table
  base := (9027180494567066078211858325423192851401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-674730869130124492338840268425000000000000)
      constant := (15592159732516589111130458416080918678313045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240853428349469504009/50000000000000000000)
  centralHi := (481706856698939008019/100000000000000000000)
  directionLo := (121072438450598853807/25000000000000000000)
  directionHi := (484289753802395415229/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree095.table
  base := (46902325876475213127988155284468593843653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-75551289701974797107658643330000000000000)
      constant := (1760491461947731133407275070742867031343653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree095.table
  base := (23451162507720527196785949061875063021739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-340956687649119549975151865422500000000000)
      constant := (7966543442813834702236172978854531817195651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121072438450598853807/25000000000000000000)
  centralHi := (484289753802395415229/100000000000000000000)
  directionLo := (30428684265246373291/6250000000000000000)
  directionHi := (486858948243941972657/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree096.table
  base := (9739595415203984926170363448585007216901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-27561289805564413181310223726385000000000000)
      constant := (649285694075777936911613812560978438026506305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree096.table
  base := (24348988165509751308932129189616008160797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-38283104525908539308987066292500000000000)
      constant := (904317706401910692516152455124616008160797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30428684265246373291/6250000000000000000)
  centralHi := (486858948243941972657/100000000000000000000)
  directionLo := (489414655821022560741/100000000000000000000)
  directionHi := (244707327910511280371/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree097.table
  base := (3157678562588312167707941082021542867971/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-13924282014357962303377838605320000000000000)
      constant := (331590890224150393803992973388597493146450248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree097.table
  base := (6315357044608720317659484303426020837921/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-348139193817234157586615327842500000000000)
      constant := (8313027610386225040440854318993805500165156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489414655821022560741/100000000000000000000)
  centralHi := (244707327910511280371/50000000000000000000)
  directionLo := (491957086725684414321/100000000000000000000)
  directionHi := (245978543362842207161/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree098.table
  base := (52376965597072388820151862881022381728169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-28135838251867436032201130694895000000000000)
      constant := (677225676860634376807183116633999079803869009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree098.table
  base := (10475393007898374837533794598266751310051/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-703460893802582922784694118105000000000000)
      constant := (16978096401760342611459999335450128808952295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491957086725684414321/100000000000000000000)
  centralHi := (245978543362842207161/50000000000000000000)
  directionLo := (494486445746326984249/100000000000000000000)
  directionHi := (1977945782985307937/400000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree099.table
  base := (5426030281556073727267779036999234633183/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-14211556237509473728823292089575000000000000)
      constant := (345708691647826907011361616999692036481645315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree099.table
  base := (13565075583313390630297668467026066720219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-39480188887260973910897643362500000000000)
      constant := (962991236543743310094607797933583383440438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494486445746326984249/100000000000000000000)
  centralHi := (1977945782985307937/400000000000000000)
  directionLo := (62125366557526214921/12500000000000000000)
  directionHi := (497002932460209719369/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree100.table
  base := (11234573723281656059097555104631529305407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-28710386698170458883092037663405000000000000)
      constant := (705756899738749515986510738676898972896259635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree100.table
  base := (28086434099624916790239847187392606564347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-358912953069406069003810521472500000000000)
      constant := (8846646394251708022979140087952158459079123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62125366557526214921/12500000000000000000)
  centralHi := (497002932460209719369/100000000000000000000)
  directionLo := (249753370708615456221/50000000000000000000)
  directionHi := (499506741417230912443/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree101.table
  base := (1452866574127639426089119141025259559883/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-14498830460660985154268745573830000000000000)
      constant := (360122113088731787276747237321010713866105260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree101.table
  base := (14528665651081878332301733986023327366631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-362504206153463372809542252682500000000000)
      constant := (9028223996805036718949528443822013642599358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249753370708615456221/50000000000000000000)
  centralHi := (499506741417230912443/100000000000000000000)
  directionLo := (501998062315456544123/100000000000000000000)
  directionHi := (125499515578864136031/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree102.table
  base := (60085685832241476792439162568964816438283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-29284935144473481733982944631915000000000000)
      constant := (734879362601178564312140916960945986234220163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree102.table
  base := (60085685520250857865359072772381388441979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-81354546497226817025616440865000000000000)
      constant := (2047034208094803340267461173976756388441979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501998062315456544123/100000000000000000000)
  centralHi := (125499515578864136031/25000000000000000000)
  directionLo := (31529817510552956857/6250000000000000000)
  directionHi := (504477080168847309713/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree103.table
  base := (31042968596382696841481656828505189899527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-14786104683812496579714199058085000000000000)
      constant := (374831154500425611883648881513509416522479247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree103.table
  base := (31042968461493912177311063239685593650041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-369686712321577980421005715102500000000000)
      constant := (9396936213008298766986867702461076592850369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31529817510552956857/6250000000000000000)
  centralHi := (504477080168847309713/100000000000000000000)
  directionLo := (253471987733801759961/50000000000000000000)
  directionHi := (506943975467603519923/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree104.table
  base := (64115417025355955078858087956015658425717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-29859483590776504584873851600425000000000000)
      constant := (764593065368784537397268246567603527691683837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree104.table
  base := (64115416792099549790682097063743128709247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-746555930811270568453474892625000000000000)
      constant := (19168141652916226085541985405026188158383223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253471987733801759961/50000000000000000000)
  centralHi := (506943975467603519923/100000000000000000000)
  directionLo := (127349731082880285789/25000000000000000000)
  directionHi := (509398924331521143157/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree105.table
  base := (33087062655940341869116916035990933467941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-15073378906964008005159652542340000000000000)
      constant := (389835815849216340458865101353733254325676701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree105.table
  base := (66174125110218112790666501381130552772971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-83748715219931686229437595005000000000000)
      constant := (2171790617043978269407338690867068052772971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127349731082880285789/25000000000000000000)
  centralHi := (509398924331521143157/100000000000000000000)
  directionLo := (51184209865672773439/10000000000000000000)
  directionHi := (511842098656727734391/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree106.table
  base := (6826206203693358909597065311016921954701/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-15217016018539763717882379284467500000000000)
      constant := (397449003992117045867337675055803356628235305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree106.table
  base := (68262061862599814715531765382887912343767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-760920943147499783676401817465000000000000)
      constant := (19927794127322639263594531676816616211093903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51184209865672773439/10000000000000000000)
  centralHi := (511842098656727734391/100000000000000000000)
  directionLo := (5142736662561442209/1000000000000000000)
  directionHi := (514273666256144220901/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree107.table
  base := (14075845437487887499775090437500817995497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-30721306260231038861210212053190000000000000)
      constant := (810272194221468610499300980083234562419372085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree107.table
  base := (17594806759185765977255400743383874230267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-384051724657807195643932639942500000000000)
      constant := (10156588687292108138710564603602940986144806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5142736662561442209/1000000000000000000)
  centralHi := (514273666256144220901/100000000000000000000)
  directionLo := (258346895496998673997/50000000000000000000)
  directionHi := (103338758198799469599/20000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree108.table
  base := (18131405188078772938428829174844835344243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-15504290241691275143327832768722500000000000)
      constant := (412897095203067612342425005586043439868543446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree108.table
  base := (3626281031103076320345116134210483505523/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-43071441971318277716629374572500000000000)
      constant := (1150125849726958803359318754763979835055230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258346895496998673997/50000000000000000000)
  centralHi := (103338758198799469599/20000000000000000000)
  directionLo := (259551316457343950627/50000000000000000000)
  directionHi := (103820526582937580251/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree109.table
  base := (74701242722179696584873071792298170886073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-31295854706534061712101119021700000000000000)
      constant := (841463996534847445536824643256051319377372353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree109.table
  base := (74701242609604557046879465095066498654921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-782468461651843606510792204725000000000000)
      constant := (21095057888745210006273706677675285987894289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259551316457343950627/50000000000000000000)
  centralHi := (103820526582937580251/20000000000000000000)
  directionLo := (52150034836630149917/10000000000000000000)
  directionHi := (521500348366301499171/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree110.table
  base := (15381218617821334502577964278618383713903/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-31583128929685573137546572505955000000000000)
      constant := (857281612604743777863140214852713995103594915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree110.table
  base := (2403315405994314993378052211584755741057/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-394825483909979107061127833572500000000000)
      constant := (10745777577748042115235669124029142326712208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52150034836630149917/10000000000000000000)
  centralHi := (521500348366301499171/100000000000000000000)
  directionLo := (523887090119031685413/100000000000000000000)
  directionHi := (261943545059515842707/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree111.table
  base := (79140171846411495277355869143617261446913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-31870403152837084562992025990210000000000000)
      constant := (873247038613411108405788825576785167319835593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree111.table
  base := (19785042940585018413342655732892808859731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (416377169166064209360200720000000000000)
      linear := (-44268526332670712318539951642500000000000)
      constant := (1216208727515590163570330858104691867719462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523887090119031685413/100000000000000000000)
  centralHi := (261943545059515842707/50000000000000000000)
  directionLo := (526263007478769146357/100000000000000000000)
  directionHi := (263131503739384573179/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree112.table
  base := (40701739494235053019720900874545254992241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-16078838687994297994218739737232500000000000)
      constant := (444680137279409575961976528614423962052199001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree112.table
  base := (16280695783165133064183333571564502124273/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-804015980156187429345182591985000000000000)
      constant := (22295663708050722287761523387675402595592285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526263007478769146357/100000000000000000000)
  centralHi := (263131503739384573179/50000000000000000000)
  directionLo := (528628246396096047989/100000000000000000000)
  directionHi := (52862824639609604799/10000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree113.table
  base := (83696014510563540410613276143939867797433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-32444951599140107413882932958720000000000000)
      constant := (905621320439264362273372011962230846962373313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree113.table
  base := (20924003611949387940724227880387177266543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-405599243162151018478323027202500000000000)
      constant := (11351637496883043266853746013589937940797774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528628246396096047989/100000000000000000000)
  centralHi := (52862824639609604799/10000000000000000000)
  directionLo := (530982949570910646041/100000000000000000000)
  directionHi := (265491474785455323021/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree114.table
  base := (86017778408744999987674784958181575445407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-90670985657317503710050931975000000000000)
      constant := (2554100211228038629447346569574431575445407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree114.table
  base := (17203555670903618836767704256206538001007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-90931221388046293840901057425000000000000)
      constant := (2568287883599230770327178430069157690005035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530982949570910646041/100000000000000000000)
  centralHi := (265491474785455323021/50000000000000000000)
  directionLo := (266663628276447199709/50000000000000000000)
  directionHi := (533327256552894399419/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree115.table
  base := (88368770679726134024607661314005513142993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-33019500045443130264773839927230000000000000)
      constant := (938586841999804806176000617448375326182120473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree115.table
  base := (88368770632879953003326339658208256940211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-825563498660531252179572979245000000000000)
      constant := (23529611583903727429249128500700436812461899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266663628276447199709/50000000000000000000)
  centralHi := (533327256552894399419/100000000000000000000)
  directionLo := (535661303838021741773/100000000000000000000)
  directionHi := (267830651919010870887/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree116.table
  base := (90748991320779764387165739683296657735987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-33306774268594641690219293411485000000000000)
      constant := (955291317677728433803434663702597905942691307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree116.table
  base := (90748991280312585702562256513742943991973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-832746004828645859791036441665000000000000)
      constant := (23948336888274903139951876926159936495927757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535661303838021741773/100000000000000000000)
  centralHi := (267830651919010870887/50000000000000000000)
  directionLo := (537985224961301376687/100000000000000000000)
  directionHi := (33624076560081336043/6250000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree117.table
  base := (93158440329656685346102558573669246341303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-33594048491746153115664746895740000000000000)
      constant := (972143603286280864844536277780286277616710383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree117.table
  base := (93158440294702316081178509306299474317931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-93325390110751163044722211565000000000000)
      constant := (2707862985054175664361060142680986974317931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537985224961301376687/100000000000000000000)
  centralHi := (33624076560081336043/6250000000000000000)
  directionLo := (108059830117185480191/20000000000000000000)
  directionHi := (135074787646481850239/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree118.table
  base := (191194235409029021516364567556282750193/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-16940661357448832270555100189997500000000000)
      constant := (494571849412398498950798661766359986954918250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree118.table
  base := (95597117674324014310019435187433111774299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-847111017164875075013963366505000000000000)
      constant := (24796901515526234778679720608971273005968691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108059830117185480191/20000000000000000000)
  centralHi := (135074787646481850239/25000000000000000000)
  directionLo := (271301604294504337537/50000000000000000000)
  directionHi := (21704128343560347003/4000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree119.table
  base := (6129063965241052065479970802117579196469/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-17084298469024587983277826932125000000000000)
      constant := (503145802146368314919890468945408361688152472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree119.table
  base := (98065023417782710205723247577655120018523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-854293523332989682625426828925000000000000)
      constant := (25226740838378309806592158821471708580166707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271301604294504337537/50000000000000000000)
  centralHi := (21704128343560347003/4000000000000000000)
  directionLo := (272448762072017800853/50000000000000000000)
  directionHi := (544897524144035601707/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree120.table
  base := (4022486301859248328929871613727994557371/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-34455871161200687392001107348505000000000000)
      constant := (1023587319689665678378210667796010775880273275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree120.table
  base := (100562157523963704309117127068940921511881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-95719558833456032248543365705000000000000)
      constant := (2851142759337085974206033394106440921511881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272448762072017800853/50000000000000000000)
  centralHi := (544897524144035601707/100000000000000000000)
  directionLo := (547182219800234796859/100000000000000000000)
  directionHi := (27359110990011739843/5000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree121.table
  base := (51544260005717347504723328563763962643233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-17371572692176099408723280416380000000000000)
      constant := (520515422507620065858226806072419317857957113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree121.table
  base := (103088519991989948534565667297198442940513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-868658535669218897848353753765000000000000)
      constant := (26097533502484733229695427128153223486464617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547182219800234796859/100000000000000000000)
  centralHi := (27359110990011739843/5000000000000000000)
  directionLo := (549457415558954003687/100000000000000000000)
  directionHi := (68682176944869250461/12500000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree122.table
  base := (105644110837975859226345416566619448496713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-35030419607503710242892014317015000000000000)
      constant := (1058622180269192332115553699237391495907313393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree122.table
  base := (5282205541059282271382450593956693481193/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-437920520918666752729908608092500000000000)
      constant := (13269243421862553007512879928803914913307370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549457415558954003687/100000000000000000000)
  centralHi := (68682176944869250461/12500000000000000000)
  directionLo := (11034464578944239343/2000000000000000000)
  directionHi := (551723228947211967151/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree123.table
  base := (10822893002554231125251897951093683776931/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-17658846915327610834168733900635000000000000)
      constant := (538180662725659628461088416445343142186110455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree123.table
  base := (108228930011045166747777291558875630026407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-98113727556160901452364519845000000000000)
      constant := (2998127206416704607742221101335438130026407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11034464578944239343/2000000000000000000)
  centralHi := (551723228947211967151/100000000000000000000)
  directionLo := (553979775088540824437/100000000000000000000)
  directionHi := (276989887544270412219/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree124.table
  base := (11084297757372297855402495059921192064791/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-17802484026903366546891460642762500000000000)
      constant := (547124140280736254475784904189652595426947755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree124.table
  base := (55421488780603260939239537608933481583079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-445103027086781360341372070512500000000000)
      constant := (13715753772278590839054937205659776334247711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553979775088540824437/100000000000000000000)
  centralHi := (276989887544270412219/50000000000000000000)
  directionLo := (556227166771241838529/100000000000000000000)
  directionHi := (55622716677124183853/10000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree125.table
  base := (113486253482234430103680610481946241160851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-35892242276958244519228374769780000000000000)
      constant := (1112283045599549769602919664018079272746567211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree125.table
  base := (56743126735714358811943304451196534048917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3747394522494577884241806480000000000000)
      linear := (-448694280170838664147103801722500000000000)
      constant := (13941787452071728850776301784963112556440253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556227166771241838529/100000000000000000000)
  centralHi := (55622716677124183853/10000000000000000000)
  directionLo := (558465514514168980987/100000000000000000000)
  directionHi := (139616378628542245247/25000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree126.table
  base := (29039689437725166957974942527233449778051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-18089758250054877972336914127017500000000000)
      constant := (565232810282743751786552892779942081989752822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree126.table
  base := (23231751548314489196117189726225121592403/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-100507896278865770656185673985000000000000)
      constant := (3148816326278657307553050210223000607962015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558465514514168980987/100000000000000000000)
  centralHi := (139616378628542245247/25000000000000000000)
  directionLo := (560694926630148927231/100000000000000000000)
  directionHi := (2190214557149019247/390625000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree127.table
  base := (59430245189817942210952152052500174027159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-18233395361630633685059640869145000000000000)
      constant := (574398002729627367210385634872140980792554399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree127.table
  base := (118860490371583617793487682284127094332649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-911753572677906543517134528285000000000000)
      constant := (28798823641650069074988614668482456348993841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560694926630148927231/100000000000000000000)
  centralHi := (2190214557149019247/390625000000000000)
  directionLo := (140728877321785109459/25000000000000000000)
  directionHi := (562915509287140437837/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree128.table
  base := (121591451368429758824785793580955395017257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (300624316137898359158064919840000000000000)
      linear := (-36754064946412778795564735222545000000000000)
      constant := (1167274200280847736247260177352274897601229777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree128.table
  base := (4863658054459173191685752909804641724383/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7494789044989155768483612960000000000000)
      linear := (-918936078846021151128597990705000000000000)
      constant := (29262005019570071493152060015306044387986175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell041.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140728877321785109459/25000000000000000000)
  centralHi := (562915509287140437837/100000000000000000000)
  directionLo := (282563683283615419571/50000000000000000000)
  directionHi := (565127366567230839143/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree129.table
  base := (31087910179333730641643384279224372315173/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (150312158068949179579032459920000000000000)
      linear := (-18520669584782145110505094353400000000000000)
      constant := (592950102515142754516734542585639274155304906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 23
  qDenominator := 48
  table := BinomialMassData.Q23_48.Degree129.table
  base := (124351640711335912053337625107285286067961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (832754338332128418720401440000000000000)
      linear := (-102902065001570639860006828125000000000000)
      constant := (3303210118918734443684315247590722786067961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23_48.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell041.Kernel129
