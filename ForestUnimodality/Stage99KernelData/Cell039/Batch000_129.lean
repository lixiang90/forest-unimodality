import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell039.Parameters
import ForestUnimodality.BinomialMassData.Q869_1824.Batch000_049
import ForestUnimodality.BinomialMassData.Q869_1824.Batch050_099
import ForestUnimodality.BinomialMassData.Q869_1824.Batch100_149
import ForestUnimodality.BinomialMassData.Q581_1216.Batch000_049
import ForestUnimodality.BinomialMassData.Q581_1216.Batch050_099
import ForestUnimodality.BinomialMassData.Q581_1216.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree000.table
  base := (5792185684476117995099997447/100000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (415142237125063623404130910000000000000)
      linear := (24376460937942587281490603000000000000)
      constant := (289609284223805899754999872350000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree000.table
  base := (5792185684476117995099997447/100000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (415142237125063623404130910000000000000)
      linear := (24376460937942587281490603000000000000)
      constant := (289609284223805899754999872350000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree001.table
  base := (335497428176126470440029448632756317523781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-2412006810764721125104476107334750000000000)
      constant := (1090567982369354333407482703086141177978514469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree001.table
  base := (334799077290994393693388072615349519278167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-268822392429279035655151354352125000000000)
      constant := (120922483482400226570400934960749292670355787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (6243049135521542601/12500000000000000000)
  directionHi := (49944393084172340809/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree002.table
  base := (202069841351809697115634235642344318214949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-4982411864704193182364078152963500000000000)
      constant := (658823197357462318491980488770040174255369301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree002.table
  base := (201308496396800617584501011428666789807771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-555244589655752619327538924070250000000000)
      constant := (72929251755168396500168751535088488464355331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6243049135521542601/12500000000000000000)
  centralHi := (49944393084172340809/100000000000000000000)
  directionLo := (70632038064129537691/100000000000000000000)
  directionHi := (17658009516032384423/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree003.table
  base := (15953807383686204787490639288509191912749/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-419600939924648068867982233255125000000000)
      constant := (23330871958761743315712788580898536793884556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree003.table
  base := (126997402561964129087716386889268547033661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-841666786882226202999926493788375000000000)
      constant := (46436666251585419915893752655220928877589121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70632038064129537691/100000000000000000000)
  centralHi := (17658009516032384423/25000000000000000000)
  directionLo := (21626556593744538247/25000000000000000000)
  directionHi := (86506226374978152989/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree004.table
  base := (42476663893316247530224640984982893927627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-5061610986291568648441641122110500000000000)
      constant := (142754176505204602124246332151136266120860123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree004.table
  base := (42237031297319128112912904533192445920921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-564044492054349893336157031753250000000000)
      constant := (15778155644697324116901854778069340164952481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21626556593744538247/25000000000000000000)
  centralHi := (86506226374978152989/100000000000000000000)
  directionLo := (6243049135521542601/6250000000000000000)
  directionHi := (99888786168344681617/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree005.table
  base := (29782437339138502073766579049222408063769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-6346813513261304677071442144924875000000000)
      constant := (104228266253628323945389217583871758096060481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree005.table
  base := (14803351133860293319673394473637473153091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-707255590667586685172350816612312500000000)
      constant := (11522317945629621184464817257104270753250452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6243049135521542601/6250000000000000000)
  centralHi := (99888786168344681617/100000000000000000000)
  directionLo := (111679058031179729887/100000000000000000000)
  directionHi := (3489970563474366559/3125000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree006.table
  base := (21861128891356847552876107740092198795561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-848001782247893411744582574193250000000000)
      constant := (9091318900814424505556289896471650952697521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree006.table
  base := (21732127656700373257669433813483259705837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-850466689280823477008544601471375000000000)
      constant := (9051733289279131022193724717418392300682157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111679058031179729887/100000000000000000000)
  centralHi := (3489970563474366559/3125000000000000000)
  directionLo := (122338278569211246161/100000000000000000000)
  directionHi := (61169139284605623081/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree007.table
  base := (831807529572704166533577105608884085947/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-8917218567200776734331044190553625000000000)
      constant := (68788153789086707068869912216603582826711060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree007.table
  base := (33078883423503997071892882643019927368497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-1987355575788120537689476772660875000000000)
      constant := (15235472277982021890320519098981450615964917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122338278569211246161/100000000000000000000)
  centralHi := (61169139284605623081/50000000000000000000)
  directionLo := (26428088696554848377/20000000000000000000)
  directionHi := (66070221741387120943/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree008.table
  base := (25964941210783044784747621433136018286961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-20404842188341025525921690426736000000000000)
      constant := (122943777740214578781923847782873173414336289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree008.table
  base := (25815217054826260838234214791961610225923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-2273777773014594121361864342379000000000000)
      constant := (13631265065786718162975015164222328791558203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26428088696554848377/20000000000000000000)
  centralHi := (66070221741387120943/50000000000000000000)
  directionLo := (141264076128259075383/100000000000000000000)
  directionHi := (17658009516032384423/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree009.table
  base := (20564817133406427778809462260931202557777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-2552805249142277509242365830262750000000000)
      constant := (12859162631054154046500473200238785217107497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree009.table
  base := (4088952429522737295263818590952767120211/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-2560199970241067705034251912097125000000000)
      constant := (12847358586401210529317136256590407737918355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141264076128259075383/100000000000000000000)
  centralHi := (17658009516032384423/12500000000000000000)
  directionLo := (5993327170100680897/4000000000000000000)
  directionHi := (74916589626258511213/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree010.table
  base := (3276124448252935104499490645342042474941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-25545652296219969640440894517993500000000000)
      constant := (113696309896782020294250839831166089380416545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree010.table
  base := (16281198434170781976084248798796164127633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-2846622167467541288706639481815250000000000)
      constant := (12635991223187426373714042508006098843825513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5993327170100680897/4000000000000000000)
  centralHi := (74916589626258511213/50000000000000000000)
  directionLo := (19742254812593287059/12500000000000000000)
  directionHi := (157938038500746296473/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree011.table
  base := (6507514841493320294014427640656956545599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-14058028675079720848850248281811125000000000)
      constant := (57772200725996811208148735849603106113526151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree011.table
  base := (12930526828742772073566533683916884332787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-3133044364694014872379027051533375000000000)
      constant := (12854929306187891825875037259378244267573607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19742254812593287059/12500000000000000000)
  centralHi := (157938038500746296473/100000000000000000000)
  directionLo := (165646812242220771923/100000000000000000000)
  directionHi := (41411703060555192981/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree012.table
  base := (2557858747164781034396002773542100921417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-1704803466894384097497783256069500000000000)
      constant := (6694889467909678320031560429957490615263074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree012.table
  base := (10158252776455884276179349145437100985941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-3419466561920488456051414621251500000000000)
      constant := (13419520301093175015976358464954152830924701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165646812242220771923/100000000000000000000)
  centralHi := (41411703060555192981/25000000000000000000)
  directionLo := (173012452749956305977/100000000000000000000)
  directionHi := (86506226374978152989/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree013.table
  base := (3941311020196221729204486691087794701991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-16628433729019192906109850327439875000000000)
      constant := (64054415820450101596662556614233118033643759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree013.table
  base := (1954613323452989742915264532417498441077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-1852944379573481019861901095484812500000000)
      constant := (7138543005430220161995777574176441198676344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173012452749956305977/100000000000000000000)
  centralHi := (86506226374978152989/50000000000000000000)
  directionLo := (180077070186912429363/100000000000000000000)
  directionHi := (45019267546728107341/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree014.table
  base := (5872309357891756528426455977655783880411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-35827272511977857869479302700508500000000000)
      constant := (138034046578093660984839445408109126202455339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree014.table
  base := (726952738061985779319354260566865053357/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-1996155478186717811698094880343875000000000)
      constant := (7696574298769966533415356462136660558922508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180077070186912429363/100000000000000000000)
  centralHi := (45019267546728107341/25000000000000000000)
  directionLo := (46718701827833697867/25000000000000000000)
  directionHi := (186874807311334791469/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree015.table
  base := (516775246983812251786875257671203167713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-2133204309217629440374383597007625000000000)
      constant := (8337125716207696242615816170691934171052572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree015.table
  base := (2041961302100002544181437046321150265593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-2139366576799954603534288665202937500000000)
      constant := (8371970631788293815989062469768915226347823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46718701827833697867/25000000000000000000)
  centralHi := (186874807311334791469/100000000000000000000)
  directionLo := (19343380265143636259/10000000000000000000)
  directionHi := (193433802651436362591/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree016.table
  base := (2620401914192742162376229681725105645233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-40968082619856801983998506791766000000000000)
      constant := (164055860044373194566489747260780868241362017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree016.table
  base := (2575729380369413257451017955894381736253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-4565155350826382790740964900124000000000000)
      constant := (18312271018438084297929859362633121806787333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19343380265143636259/10000000000000000000)
  centralHi := (193433802651436362591/100000000000000000000)
  directionLo := (199777572336689363233/100000000000000000000)
  directionHi := (99888786168344681617/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree017.table
  base := (323713355327381662390857199907391283749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-21769243836898137020629054418697375000000000)
      constant := (89939846449607534497640456528037617233676002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree017.table
  base := (1255150582714704993996062281191101330767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-4851577548052856374413352469842125000000000)
      constant := (20085180976369947589721739768650072541344387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199777572336689363233/100000000000000000000)
  centralHi := (99888786168344681617/50000000000000000000)
  directionLo := (205926008093410758149/100000000000000000000)
  directionHi := (4118520161868215163/2000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree018.table
  base := (129522643810412227545308313460046090083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-5123210303081749566501967875891500000000000)
      constant := (21938742162948182059521644852129436013519963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree018.table
  base := (18851115738746727956470286818690579233/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-5137999745279329958085740039560250000000000)
      constant := (22052588179024462563737914473556201339265565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205926008093410758149/100000000000000000000)
  centralHi := (4118520161868215163/2000000000000000000)
  directionLo := (105948057096194306537/50000000000000000000)
  directionHi := (8475844567695544523/4000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree019.table
  base := (-448958344089213753493992646263872540217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (522)
      previous := (261)
      next := (261)
      square := (3736280134125572610637178190000000000000)
      linear := (-67422850113123570852877164721125000000000)
      constant := (300125043899596732968667181478388819013047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree019.table
  base := (-929212435898690883105678202558418137939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (830284474250127246808261820000000000000)
      linear := (-15026099563727987650299522463375000000000)
      constant := (67053900055633118010667216098495292799561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105948057096194306537/50000000000000000000)
  centralHi := (8475844567695544523/4000000000000000000)
  directionLo := (108851281125189469401/50000000000000000000)
  directionHi := (217702562250378938803/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree020.table
  base := (-1805551294825671247358071297082667175093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-51249702835614690213036914974281000000000000)
      constant := (237545735832312639923727676094115601848122843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree020.table
  base := (-458322308798621123473913827431282722319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-2855422069866138562715257589498250000000000)
      constant := (13270139642542802528609708714412543561985682) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108851281125189469401/50000000000000000000)
  centralHi := (217702562250378938803/100000000000000000000)
  directionLo := (8934324642494378391/4000000000000000000)
  directionHi := (3489970563474366559/1562500000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree021.table
  base := (-2608207476311170392665000871593131663901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-5980011987728240252255168557767750000000000)
      constant := (28885207914184521944563183401497844313081739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree021.table
  base := (-2632760383454363173358104162385604687253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-5997266336958750709102902748714625000000000)
      constant := (29048714685332492460785412462093670731339167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8934324642494378391/4000000000000000000)
  centralHi := (3489970563474366559/1562500000000000000)
  directionLo := (22887396184684871411/10000000000000000000)
  directionHi := (228873961846848714111/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree022.table
  base := (-3318137406354940271455176468561608324259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-56390512943493634327556119065538500000000000)
      constant := (283913880569136684132953367017311193929482509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree022.table
  base := (-834960787251719860337338773513713922283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-3141844267092612146387645159216375000000000)
      constant := (15863676843478805176440357430481815344986674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22887396184684871411/10000000000000000000)
  centralHi := (228873961846848714111/100000000000000000000)
  directionLo := (234259968436818250149/100000000000000000000)
  directionHi := (4685199368736365003/2000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree023.table
  base := (-1972761075755325545256841290207074644333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-29480458998716553192407860555583625000000000)
      constant := (154676842785753862658768542894857571902437083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree023.table
  base := (-1982343655724692194879737012258782994783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-3285055365705848938223838944075437500000000)
      constant := (17286266109763157494666505414196348381852087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234259968436818250149/100000000000000000000)
  centralHi := (4685199368736365003/2000000000000000000)
  directionLo := (59881223691448873031/25000000000000000000)
  directionHi := (1916199158126363937/800000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree024.table
  base := (-4498854222848319043584215099078652951927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-6836813672374730938008369239644000000000000)
      constant := (37362077118478593160149615441979856284354353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree024.table
  base := (-4515756656421638914334913072835047670637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-6856532928638171460120065457869000000000000)
      constant := (37581194856422652686777831149399735290900043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59881223691448873031/25000000000000000000)
  centralHi := (1916199158126363937/800000000000000000)
  directionLo := (244676557138422492323/100000000000000000000)
  directionHi := (61169139284605623081/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree025.table
  base := (-4985236900898970897086572331776125556331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-64101728105312050499334925202424750000000000)
      constant := (364605827495090217540283801881460832911230581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree025.table
  base := (-2500063915736947396196534660493836012189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-3571477562932322521896226513793562500000000)
      constant := (20375393463940491276801797738694916117568521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244676557138422492323/100000000000000000000)
  centralHi := (61169139284605623081/25000000000000000000)
  directionLo := (249721965420861704041/100000000000000000000)
  directionHi := (124860982710430852021/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree026.table
  base := (-2705311679013194404017216895635553784771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-33336066579625761278297263624026750000000000)
      constant := (197187872000423217193105714881834765440779021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree026.table
  base := (-1084745855624915386769358626979668066073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-7429377323091118627464840597305250000000000)
      constant := (44079168266513153197331764830264820234488235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249721965420861704041/100000000000000000000)
  centralHi := (124860982710430852021/50000000000000000000)
  directionLo := (127333717465371647901/50000000000000000000)
  directionHi := (254667434930743295803/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree027.table
  base := (-5780010507829957678561275847466922226853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-7693615357021221623761569921520250000000000)
      constant := (47283578734587954159121973099847655919856067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree027.table
  base := (-144788375185659039234239775716121495089/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-3857899760158796105568614083511687500000000)
      constant := (23782271627164574249344601678221305442176170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127333717465371647901/50000000000000000000)
  centralHi := (254667434930743295803/100000000000000000000)
  directionLo := (129759339562467229483/50000000000000000000)
  directionHi := (259518679124934458967/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree028.table
  base := (-6097597754502517546806077030505124653361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-71812943267130466671113731339311000000000000)
      constant := (458121577462203139394029245041909037501230111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree028.table
  base := (-1526930827801962161178347852996594965693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-4001110858772032897404807868370750000000000)
      constant := (25602701763989421938629732450000075622269654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129759339562467229483/50000000000000000000)
  centralHi := (259518679124934458967/100000000000000000000)
  directionLo := (26428088696554848377/10000000000000000000)
  directionHi := (264280886965548483771/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree029.table
  base := (-6366917906673278529158893295444510706981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-74383348321069938728373333384939750000000000)
      constant := (492072372458344786603854599395523905806768731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree029.table
  base := (-1593951909201527473314863489082123939043/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-4144321957385269689241001653229812500000000)
      constant := (27500240366486778218645957359780010715229704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26428088696554848377/10000000000000000000)
  centralHi := (264280886965548483771/100000000000000000000)
  directionLo := (67239696987644200163/25000000000000000000)
  directionHi := (268958787950576800653/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree030.table
  base := (-3295472828980831518580369412650664139729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-4275208520833856154757385301698250000000000)
      constant := (29299718267785945869248725882158539933057831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree030.table
  base := (-3299372506856835027398613662118934363609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-4287533055998506481077195438088875000000000)
      constant := (29474353690833242373861280923967828366612151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67239696987644200163/25000000000000000000)
  centralHi := (268958787950576800653/100000000000000000000)
  directionLo := (54711341426212411359/20000000000000000000)
  directionHi := (68389176782765514199/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree031.table
  base := (-6772187783990108649218618419700690289301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-79524158428948882842892537476197250000000000)
      constant := (564081102033612556829652285897916484593811051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree031.table
  base := (-3389513089670326422231147753052231570597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-4430744154611743272913389222947937500000000)
      constant := (31524592158926287073693730232298140008483233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54711341426212411359/20000000000000000000)
  centralHi := (68389176782765514199/25000000000000000000)
  directionLo := (55615722387445793313/20000000000000000000)
  directionHi := (139039305968614483283/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree032.table
  base := (-1382551664455151469785571137227134888249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-82094563482888354900152139521826000000000000)
      constant := (602124023590848185848679053051967193740394995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree032.table
  base := (-3459375336379200557135602321026829095741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-4573955253224980064749583007807000000000000)
      constant := (33650576803963534933354318706478314696437499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55615722387445793313/20000000000000000000)
  centralHi := (139039305968614483283/50000000000000000000)
  directionLo := (141264076128259075383/50000000000000000000)
  directionHi := (282528152256518150767/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree033.table
  base := (-7014441351740512861848577756820519579333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-9407218726314202995267971285272750000000000)
      constant := (71279766335492960833245834920937976025610787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree033.table
  base := (-3509844758682277715714533058831311015237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-4717166351838216856585776792666062500000000)
      constant := (35851987956221711830462523741411673578968193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141264076128259075383/50000000000000000000)
  centralHi := (282528152256518150767/100000000000000000000)
  directionLo := (17931793432209292357/6250000000000000000)
  directionHi := (286908694915348677713/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree034.table
  base := (-1415748698822986168914331282622429987949/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-87235373590767299014671343613083500000000000)
      constant := (682257827305375366452988927189711609220768495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree034.table
  base := (-1770834404779688117868118515814421183109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-4860377450451453648421970577525125000000000)
      constant := (38128555785175103345083990096574314077670302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17931793432209292357/6250000000000000000)
  centralHi := (286908694915348677713/100000000000000000000)
  directionLo := (5824467069821064621/2000000000000000000)
  directionHi := (291223353491053231051/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree035.table
  base := (-7106937873214507132812458996103867146453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-89805778644706771071930945658712250000000000)
      constant := (724339678069387796739769063264564531734924203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree035.table
  base := (-7110957620180818436423322789394359714791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-10007177098129380880516328724768375000000000)
      constant := (80960104767827721695507531697821932041397949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5824467069821064621/2000000000000000000)
  centralHi := (291223353491053231051/100000000000000000000)
  directionLo := (295475014204452265531/100000000000000000000)
  directionHi := (73868753551113066383/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree036.table
  base := (-7100100960473820206887701833582038717521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-10264020410960693681021171967149000000000000)
      constant := (85306661317309221430778212351558071522974919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree036.table
  base := (-3551808319716982502801528165304067303951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-5146799647677927232094358147243250000000000)
      constant := (42906285137479564630354330350187973890773689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295475014204452265531/100000000000000000000)
  centralHi := (73868753551113066383/25000000000000000000)
  directionLo := (5993327170100680897/2000000000000000000)
  directionHi := (299666358505034044851/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree037.table
  base := (-705914348688589853073420668822156769809/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-47473294376292857593225074874984875000000000)
      constant := (406257844849782302692681368490577592571327795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree037.table
  base := (-1412443416473620056365226063471837206103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-10580021492582328047861103864204625000000000)
      constant := (90814182323362572560655348718214551616421585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5993327170100680897/2000000000000000000)
  centralHi := (299666358505034044851/100000000000000000000)
  directionLo := (37974985356361131513/12500000000000000000)
  directionHi := (60759976570177810421/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree038.table
  base := (-1396967279856084288762800887134310887287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7472560268251145221274356380000000000000)
      linear := (-270130176749377249982575489738500000000000)
      constant := (2378405503585825501636934632689690385072085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree038.table
  base := (-6987522499899752675248556960345293087279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (830284474250127246808261820000000000000)
      linear := (-30100952049331860475162026132750000000000)
      constant := (265830097704036523100502147765307050662721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37974985356361131513/12500000000000000000)
  centralHi := (60759976570177810421/20000000000000000000)
  directionLo := (15393895804892944149/5000000000000000000)
  directionHi := (307877916097858882981/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree039.table
  base := (-3438916336543086152773265728299999261511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-5560411047803592183387186324512625000000000)
      constant := (50334662312409448769942342145705635813469529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree039.table
  base := (-6880179309349484924602508737121153230823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-11152865887035275215205879003640875000000000)
      constant := (101263785761690242947904126311162583019610397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15393895804892944149/5000000000000000000)
  centralHi := (307877916097858882981/100000000000000000000)
  directionLo := (9746957338808720951/3125000000000000000)
  directionHi := (311902634841879070433/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree040.table
  base := (-168467141429658877507815339676644590331/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-51328901957202065679114477943428000000000000)
      constant := (477386248177852145472097851252484759520291620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree040.table
  base := (-6740735053812399140244989782030135439741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-11439288084261748798878266573359000000000000)
      constant := (106711346131904415024685023129376808606253499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9746957338808720951/3125000000000000000)
  centralHi := (311902634841879070433/100000000000000000000)
  directionLo := (63175215400298518589/20000000000000000000)
  directionHi := (157938038500746296473/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree041.table
  base := (-6567864513668193583390554552216945292313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-105228208968343603415488557932484750000000000)
      constant := (1004848586683864255365734825244776484589025063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree041.table
  base := (-6569653763008384600583458479738128229557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-11725710281488222382550654143077125000000000)
      constant := (112307178867070821040118873321054136295067423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63175215400298518589/20000000000000000000)
  centralHi := (157938038500746296473/50000000000000000000)
  directionLo := (319800153881137461459/100000000000000000000)
  directionHi := (15990007694056873073/5000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree042.table
  base := (-127315344436935399219840955621768432623/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-5988811890126837526263786665450750000000000)
      constant := (58680605531836403835310985271732657083077425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree042.table
  base := (-1591832221256322610450888181844813356487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-6006066239357347983111520856397625000000000)
      constant := (59025570966214873728021330802664574053491386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319800153881137461459/100000000000000000000)
  centralHi := (15990007694056873073/5000000000000000000)
  directionLo := (323676660917875760421/100000000000000000000)
  directionHi := (161838330458937880211/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree043.table
  base := (-1226546307687220972907152442703265203977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-110369019076222547530007762023742250000000000)
      constant := (1108978337651713478922305176058676015355143635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree043.table
  base := (-6134094180681744982494781780123318432901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-12298554675941169549895429282513375000000000)
      constant := (123943114840325669449445575141085543569160239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323676660917875760421/100000000000000000000)
  centralHi := (161838330458937880211/50000000000000000000)
  directionLo := (81876821820758530391/25000000000000000000)
  directionHi := (65501457456606824313/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree044.table
  base := (-2934522120671790679405880640758333738551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-56469712065081009793633682034685500000000000)
      constant := (581514984589208898724177116328310517433447801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree044.table
  base := (-5870232907716863724372693297802619002079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-12584976873167643133567816852231500000000000)
      constant := (129982995334714766324208301223123863915249481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81876821820758530391/25000000000000000000)
  centralHi := (65501457456606824313/20000000000000000000)
  directionLo := (331293624484441543847/100000000000000000000)
  directionHi := (41411703060555192981/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree045.table
  base := (-1114989786198789894513490175016470851319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-12834425464900165738280774012777750000000000)
      constant := (135378333632820912418927175883159547457119205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree045.table
  base := (-1393996392091334515129920019314604228287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-6435699535197058358620102210974812500000000)
      constant := (68085348297145157243714048025892206821395536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331293624484441543847/100000000000000000000)
  centralHi := (41411703060555192981/12500000000000000000)
  directionLo := (167518587046769594831/50000000000000000000)
  directionHi := (335037174093539189663/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree046.table
  base := (-5250652618477951424875270017783300002129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-118080234238040963701786568160628500000000000)
      constant := (1275102765623590900418509872546542042668082879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree046.table
  base := (-2625778224609597374645894634799688189739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-6578910633810295150456295995833875000000000)
      constant := (71253072435796296139669213302758482485379221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167518587046769594831/50000000000000000000)
  centralHi := (335037174093539189663/100000000000000000000)
  directionLo := (169369677351888175491/50000000000000000000)
  directionHi := (338739354703776350983/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree047.table
  base := (-2448165646316692113407849729789899472193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-60325319645990217879523085103128625000000000)
      constant := (666561343087645930451924809747159192786719943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree047.table
  base := (-4897119145068536710177769347535803769029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-13444243464847063884584979561385875000000000)
      constant := (148989277498902372546003854685673097300318031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169369677351888175491/50000000000000000000)
  centralHi := (338739354703776350983/100000000000000000000)
  directionLo := (2739212065693953607/800000000000000000)
  directionHi := (85600377052936050219/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree048.table
  base := (-70502103549049437085129403116321835423/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-6845613574773328212016987347327000000000000)
      constant := (77359126558928238601861964993761250157193504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree048.table
  base := (-564102653422757720964827202796746300569/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-6865332831036768734128683565552000000000000)
      constant := (77810020601459727686382540131435623341978364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2739212065693953607/800000000000000000)
  centralHi := (85600377052936050219/25000000000000000000)
  directionLo := (69204981099982522391/20000000000000000000)
  directionHi := (86506226374978152989/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree049.table
  base := (-2049094981396264702183055473866027635961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-62895724699929689936782687148757375000000000)
      constant := (726563563774794986771284580805976539882637711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree049.table
  base := (-4098788192185751582700809166591138617577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-14017087859300011051929754700822125000000000)
      constant := (162398390679578461380078185835947121419992203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69204981099982522391/20000000000000000000)
  centralHi := (86506226374978152989/25000000000000000000)
  directionLo := (174805375794603192829/50000000000000000000)
  directionHi := (349610751589206385659/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree050.table
  base := (-913651419620921170550163851315755927671/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-64180927226899425965412488171571750000000000)
      constant := (757555441259461311853310676753951585169493842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree050.table
  base := (-3655126800458624948571544890783340766651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-14303510056526484635602142270540250000000000)
      constant := (169324287388165964783508731876175553826988989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174805375794603192829/50000000000000000000)
  centralHi := (349610751589206385659/100000000000000000000)
  directionLo := (176580095160323844229/50000000000000000000)
  directionHi := (353160190320647688459/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree051.table
  base := (-1590737023133652429913339031554639128133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-7274014417096573554893587688265125000000000)
      constant := (87689735732044478115493435607914476446618987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree051.table
  base := (-318192790607124824087467833700094845853/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-7294966126876479109637264920129187500000000)
      constant := (88198849265217345560742693627438179877454085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176580095160323844229/50000000000000000000)
  centralHi := (353160190320647688459/100000000000000000000)
  directionLo := (178337154308813632593/50000000000000000000)
  directionHi := (356674308617627265187/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree052.table
  base := (-2678873650765116570945717301616981538197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-133502664561677796045344180434401000000000000)
      constant := (1643039954201787930826454325717880614482397947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree052.table
  base := (-334908606394035508919472839643763285359/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-7438177225489715901473458704988250000000000)
      constant := (91809298092938096595584000021275710503441604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178337154308813632593/50000000000000000000)
  centralHi := (356674308617627265187/100000000000000000000)
  directionLo := (360154140373824858727/100000000000000000000)
  directionHi := (45019267546728107341/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree053.table
  base := (-429374288085558357085370040174645488189/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-136073069615617268102603782480029750000000000)
      constant := (1708984798078368364719234176400960317638119695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree053.table
  base := (-85888619843547706824286196880020561699/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-15162776648205905386619304979694625000000000)
      constant := (190986956578890778349312751061632875954104025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360154140373824858727/100000000000000000000)
  centralHi := (45019267546728107341/12500000000000000000)
  directionLo := (181800335003098291249/50000000000000000000)
  directionHi := (363600670006196582499/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree054.table
  base := (-792762233765250953845350707077656232301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-7702415259419818897770188029203250000000000)
      constant := (98680532746872215325792154638511208287639339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree054.table
  base := (-158582394073796937742587250789786076823/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-7724599422716189485145846274706375000000000)
      constant := (99251379728714945389306947657139965428209485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181800335003098291249/50000000000000000000)
  centralHi := (363600670006196582499/100000000000000000000)
  directionLo := (91753708926908434621/25000000000000000000)
  directionHi := (73402967141526747697/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree055.table
  base := (-248720341209088508052439112717572268537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-70606939861748106108561493285643625000000000)
      constant := (922417085144967564655793520787270697820921574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree055.table
  base := (-31098187016152407481864051617809178449/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-7867810521329426276982040059565437500000000)
      constant := (103082993782952039545542523991310834478247326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91753708926908434621/25000000000000000000)
  centralHi := (73402967141526747697/20000000000000000000)
  directionLo := (46299691553718750683/12500000000000000000)
  directionHi := (74079506485950001093/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree056.table
  base := (-93745899838550876768694762382622922029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-71892142388717842137191294308458000000000000)
      constant := (957369202945381177017636029629276341252655558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree056.table
  base := (-375210365548599378896028702066029965107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-16022043239885326137636467688849000000000000)
      constant := (213976626197850873962973186278867850682596373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46299691553718750683/12500000000000000000)
  centralHi := (74079506485950001093/20000000000000000000)
  directionLo := (46718701827833697867/12500000000000000000)
  directionHi := (373749614622669582937/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree057.table
  base := (274133462692194903335150291218134707959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (830284474250127246808261820000000000000)
      linear := (-45046072585834150917710738892750000000000)
      constant := (611253364524875521947013297631620478457959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree057.table
  base := (2140126462776977513755798617236091673/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (415142237125063623404130910000000000000)
      linear := (-22587902267467866650012264901062500000000)
      constant := (307388729662224426883847086748401059085822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46718701827833697867/12500000000000000000)
  centralHi := (373749614622669582937/100000000000000000000)
  directionLo := (75414379751116524283/20000000000000000000)
  directionHi := (47133987344447827677/12500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree058.table
  base := (476219825436588874841710534538690372163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-74462547442657314194450896354086750000000000)
      constant := (1029252699308941901538207414146160634706657587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree058.table
  base := (952268060427123191674766008794358710663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-16594887634338273304981242828285250000000000)
      constant := (230040086730289221057792080184665259588299343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75414379751116524283/20000000000000000000)
  centralHi := (47133987344447827677/12500000000000000000)
  directionLo := (380365165639135089321/100000000000000000000)
  directionHi := (190182582819567544661/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree059.table
  base := (1659909221195812501243960761086162619241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-151495499939254100446161394753802250000000000)
      constant := (2132367974078219013054648922493011125943664009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree059.table
  base := (331951999347926149510076740056032131011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-16881309831564746888653630398003375000000000)
      constant := (238292888822459900895866904053065355769912355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380365165639135089321/100000000000000000000)
  centralHi := (190182582819567544661/50000000000000000000)
  directionLo := (191815081284184348391/50000000000000000000)
  directionHi := (383630162568368696783/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree060.table
  base := (1198260100898522792058161838302326352919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-8559216944066309583523388711079500000000000)
      constant := (122641657574207952204385885475461983563403759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree060.table
  base := (2396390449448137292266637284245860058081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-17167732028791220472326017967721500000000000)
      constant := (246693061314270409026901402394774239855967241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191815081284184348391/50000000000000000000)
  centralHi := (383630162568368696783/100000000000000000000)
  directionLo := (19343380265143636259/5000000000000000000)
  directionHi := (386867605302872725181/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree061.table
  base := (3162253836274260121717581597801375513097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-156636310047133044560680598845059750000000000)
      constant := (2284050924450904080717287942708500540135802153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree061.table
  base := (3162141033401340510429496353497159715807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-17454154226017694055998405537439625000000000)
      constant := (255240597568681125315038330232794770555843827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19343380265143636259/5000000000000000000)
  centralHi := (386867605302872725181/100000000000000000000)
  directionLo := (195039089949505787947/50000000000000000000)
  directionHi := (78015635979802315179/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree062.table
  base := (1978547054956812797615111716753553980143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-79603357550536258308970100445344250000000000)
      constant := (1180935593195948300407018420704178414068984607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree062.table
  base := (123656126812203915985664994422666238383/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-8870288211622083819835396553578875000000000)
      constant := (131967745960691151806304012347448646364775208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195039089949505787947/50000000000000000000)
  centralHi := (78015635979802315179/20000000000000000000)
  directionLo := (98315636101878512627/25000000000000000000)
  directionHi := (393262544407514050509/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree063.table
  base := (4781027346332798835343321449594519321619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-17975235572779109852799978104035250000000000)
      constant := (271223397524906051890233492272189430068854459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree063.table
  base := (2390471064852274560356920959372819455559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-9013499310235320611671590338437937500000000)
      constant := (136388869768658210725037932579130864678925549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98315636101878512627/25000000000000000000)
  centralHi := (393262544407514050509/100000000000000000000)
  directionLo := (79284266089664545131/20000000000000000000)
  directionHi := (49552666306040340707/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree064.table
  base := (5634041863959759295161157807732163429179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-164347525208951460732459404981946000000000000)
      constant := (2521469060494250184554617522575805798981402571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree064.table
  base := (5633967813791757302916776736388272327053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-18313420817697114807015568246594000000000000)
      constant := (281767336288538131504195875089822166310066133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79284266089664545131/20000000000000000000)
  centralHi := (49552666306040340707/12500000000000000000)
  directionLo := (399555144673378726467/100000000000000000000)
  directionHi := (99888786168344681617/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree065.table
  base := (1303225536675884064610112639926807413949/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-166917930262890932789719007027574750000000000)
      constant := (2603246602279064136910428950704038388783351505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree065.table
  base := (1303212669229658540167198212818895362719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-18599843014923588390687955816312125000000000)
      constant := (290904278650205941341177666840639097340645295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399555144673378726467/100000000000000000000)
  centralHi := (99888786168344681617/25000000000000000000)
  directionLo := (201332285063468476021/50000000000000000000)
  directionHi := (402664570126936952043/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree066.table
  base := (7427276277940761457676073175692652376263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-18832037257425600538553178785911500000000000)
      constant := (298482575041723017622295198981958656882830943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree066.table
  base := (1856805096975795839789019777576678318437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-9443132606075030987180171693015125000000000)
      constant := (150094281805993715042576189459980125417786514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201332285063468476021/50000000000000000000)
  centralHi := (402664570126936952043/100000000000000000000)
  directionLo := (40575016751205075551/10000000000000000000)
  directionHi := (405750167512050755511/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree067.table
  base := (2091870090292171222988427846132914325283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-86029370185384938452119105559416125000000000)
      constant := (1385379378054910828425042601905476300332563934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree067.table
  base := (8367431816312969085517615440863562919653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-19172687409376535558032730955748375000000000)
      constant := (309620188602572208606678258746053354612432233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40575016751205075551/10000000000000000000)
  centralHi := (405750167512050755511/100000000000000000000)
  directionLo := (408812476371017290323/100000000000000000000)
  directionHi := (102203119092754322581/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree068.table
  base := (116709171318743185544517768782101726243/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-87314572712354674480748906582230500000000000)
      constant := (1428246662124326527050974914314345784092540280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree068.table
  base := (4668345773272600615727879211162192530193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-9729554803301504570852559262733250000000000)
      constant := (159599575712667881471829749244623168690899673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408812476371017290323/100000000000000000000)
  centralHi := (102203119092754322581/25000000000000000000)
  directionLo := (205926008093410758149/50000000000000000000)
  directionHi := (411852016186821516299/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree069.table
  base := (1033503098768403160039014808168428010179/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-9844419471036045612153189733893875000000000)
      constant := (163530381249820290018422685785550557480248095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree069.table
  base := (10334994379748424283664385067194509315263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-19745531803829482725377506095184625000000000)
      constant := (328925450203492717655792587751053623136247443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205926008093410758149/50000000000000000000)
  centralHi := (411852016186821516299/100000000000000000000)
  directionLo := (414869287411946431997/100000000000000000000)
  directionHi := (207434643705973215999/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree070.table
  base := (5681183828451536820292004118704191816971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-89884977766294146538008508627859250000000000)
      constant := (1515959678034273057467275493426479723900838779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree070.table
  base := (11362335873499343251743944001869310987779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-20031954001055956309049893664902750000000000)
      constant := (338799083333328263251543288485603942360338219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414869287411946431997/100000000000000000000)
  centralHi := (207434643705973215999/50000000000000000000)
  directionLo := (20893238621515964977/5000000000000000000)
  directionHi := (417864772430319299541/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree071.table
  base := (99349918577843085629613444204010826557/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-182340360586527765133276619301347250000000000)
      constant := (3121610792322376529509603903395506986779211625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree071.table
  base := (12418712231305247881662198344330203776507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-20318376198282429892722281234620875000000000)
      constant := (348820049444308531329205963178488585399256527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20893238621515964977/5000000000000000000)
  centralHi := (417864772430319299541/100000000000000000000)
  directionLo := (420838936457629664167/100000000000000000000)
  directionHi := (52604867057203708021/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree072.table
  base := (13504144156584589363804272940268477506743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-20545640626718581910059580149664000000000000)
      constant := (356957906716507673950099070404561170379934223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree072.table
  base := (1350412020833777777420552934781891251187/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-10302399197754451738197334402169500000000000)
      constant := (179494173682525241892332247731063907458392535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420838936457629664167/100000000000000000000)
  centralHi := (52604867057203708021/12500000000000000000)
  directionLo := (423792228384777226149/100000000000000000000)
  directionHi := (8475844567695544523/2000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree073.table
  base := (7309288907367825026714049976320015228297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-93740585347203354623897911696302375000000000)
      constant := (1652475225601485670374362331652821274398611953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree073.table
  base := (14618557030996565788535557491189631210527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-20891220592735377060067056374057125000000000)
      constant := (369303976094284388080076230329387994952937747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423792228384777226149/100000000000000000000)
  centralHi := (8475844567695544523/2000000000000000000)
  directionLo := (426725081568779481557/100000000000000000000)
  directionHi := (213362540784389740779/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree074.table
  base := (3152407672659060582450308828968750694501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-190051575748346181305055425438233500000000000)
      constant := (3398598656679504882571918057398940964407168745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree074.table
  base := (7881010164129909578588339104565295409451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-10588821394980925321869721971887625000000000)
      constant := (189883467388035688513191237266095788439686811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426725081568779481557/100000000000000000000)
  centralHi := (213362540784389740779/50000000000000000000)
  directionLo := (429637914575084753361/100000000000000000000)
  directionHi := (214818957287542376681/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree075.table
  base := (4233630930232061539311958423234189650059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-10701221155682536297906390415770125000000000)
      constant := (194086987228661738640412101903608629849217598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree075.table
  base := (8467254036541648868028352233617492769153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-10732032493594162113705915756746687500000000)
      constant := (195188611339324239965786584275558851901382983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429637914575084753361/100000000000000000000)
  centralHi := (214818957287542376681/50000000000000000000)
  directionLo := (27033195742180672809/6250000000000000000)
  directionHi := (86506226374978152989/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree076.table
  base := (18136032107282546636697249725124108353597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7472560268251145221274356380000000000000)
      linear := (-540699129795637466536217810331000000000000)
      constant := (9944187772099244179516029438474304475182373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree076.table
  base := (3627203706473541318555328387379022860301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (830284474250127246808261820000000000000)
      linear := (-60250657020539606124887033471500000000000)
      constant := (1111176839823730890097097715882379489301505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27033195742180672809/6250000000000000000)
  centralHi := (86506226374978152989/20000000000000000000)
  directionLo := (87081024900151575521/20000000000000000000)
  directionHi := (217702562250378938803/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree077.table
  base := (4841640499840016916347916147249230017091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-98881395455082298738417115787559875000000000)
      constant := (1843728349283515748157641614864535119697932318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree077.table
  base := (19366550224234228944084597065341333081219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-22036909381641271394756606652929625000000000)
      constant := (412039783734268238348065861606905610890757559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87081024900151575521/20000000000000000000)
  centralHi := (217702562250378938803/50000000000000000000)
  directionLo := (219130135331762841143/50000000000000000000)
  directionHi := (438260270663525682287/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree078.table
  base := (20626112094236835964804846902841038591601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-22259243996011563281565981513416500000000000)
      constant := (420708944933369372097275101758367224306567961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree078.table
  base := (10313050940767347716958891371406786409081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-11161665789433872489214497111323875000000000)
      constant := (211546027947456075931537630462297082315553241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219130135331762841143/50000000000000000000)
  centralHi := (438260270663525682287/100000000000000000000)
  directionLo := (55137117041661054467/12500000000000000000)
  directionHi := (441096936333288435737/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree079.table
  base := (21914681277204147464837181044844761673531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-202903601018043541591353435666377250000000000)
      constant := (3886623199606017126962111034422662033021052219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree079.table
  base := (876586896827268584469928193623134377231/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-22609753776094218562101381792365875000000000)
      constant := (434291655267123543556439867506131872715447275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55137117041661054467/12500000000000000000)
  centralHi := (441096936333288435737/100000000000000000000)
  directionLo := (22195773789347795211/5000000000000000000)
  directionHi := (443915475786955904221/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree080.table
  base := (23232268594538132542415023291474415149597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-205474006071983013648613037712006000000000000)
      constant := (3988184781085460978169822317063380374821040653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree080.table
  base := (232322609150192057750456909482114272767/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-11448087986660346072886884681042000000000000)
      constant := (222819290758189784147273144555677787623444350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22195773789347795211/5000000000000000000)
  centralHi := (443915475786955904221/100000000000000000000)
  directionLo := (8934324642494378391/2000000000000000000)
  directionHi := (446716232124718919551/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree081.table
  base := (6144718307555517288192945347572500221243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-11558022840329026983659591097646375000000000)
      constant := (227281402565967642920842394751071249456612446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree081.table
  base := (19663093257655007041439981248832943689/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-11591299085273582864723078465901062500000000)
      constant := (228566417178297760011674410127039412900299375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8934324642494378391/2000000000000000000)
  centralHi := (446716232124718919551/100000000000000000000)
  directionLo := (17979981510302042691/4000000000000000000)
  directionHi := (112374884439387766819/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree082.table
  base := (2595449448604500545373176312409126940657/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-105307408089930978881566120901631750000000000)
      constant := (2097632296321699763821452287888342384338472965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree082.table
  base := (25954488714085128280290350891574994047679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-23469020367773639313118544501520250000000000)
      constant := (468774413543105365149216284340016787694962119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17979981510302042691/4000000000000000000)
  centralHi := (112374884439387766819/25000000000000000000)
  directionLo := (113066428716926847/25000000000000000)
  directionHi := (452265714867707388001/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree083.table
  base := (1367956588229241230111508905017052380519/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-106592610616900714910195921924446125000000000)
      constant := (2150391409256191192874964611925116967389937310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree083.table
  base := (13679563380718760323456684401131745356393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-11877721282500056448395466035619187500000000)
      constant := (240281659433331193597843918837257067397876623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113066428716926847/25000000000000000)
  centralHi := (452265714867707388001/100000000000000000000)
  directionLo := (91003015168805197441/20000000000000000000)
  directionHi := (227507537922012993603/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree084.table
  base := (179954903466599703183502090916535871777/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-11986423682652272326536191438584500000000000)
      constant := (244867773451862456482298844898412399726919760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree084.table
  base := (28792780218404331757368235695123175340923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-24041864762226586480463319640956500000000000)
      constant := (492499550148311087066670893407698825673073203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91003015168805197441/20000000000000000000)
  centralHi := (227507537922012993603/50000000000000000000)
  directionLo := (22887396184684871411/5000000000000000000)
  directionHi := (457747923693697428221/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree085.table
  base := (1210218096754533625222672483032921648961/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-218326031341680373934911047940149750000000000)
      constant := (4515775902085728507715993967902297244530607225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree085.table
  base := (30255448661029486368764639760996293971629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-24328286959453060064135707210674625000000000)
      constant := (504583107235003321599482048976464911147195569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22887396184684871411/5000000000000000000)
  centralHi := (457747923693697428221/100000000000000000000)
  directionLo := (57558069054004789759/12500000000000000000)
  directionHi := (460464552432038318073/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree086.table
  base := (31747134982956734693355285761258261773719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-220896436395619845992170649985778500000000000)
      constant := (4625250757153056182722439441356284951877813031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree086.table
  base := (3174713172674008874223117300886244615387/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-12307354578339766823904047390196375000000000)
      constant := (258406994997925137716194363048027013327648535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57558069054004789759/12500000000000000000)
  centralHi := (460464552432038318073/100000000000000000000)
  directionLo := (463165247451688334557/100000000000000000000)
  directionHi := (231582623725844167279/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree087.table
  base := (16633915963361956162894351296953734774849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-12414824524975517669412791779522625000000000)
      constant := (263113582571952096178571785739277921300595489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree087.table
  base := (8316957276367261640161891202052941857573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-12450565676953003615740241175055437500000000)
      constant := (264596099159458864119455253534426055564136456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463165247451688334557/100000000000000000000)
  centralHi := (231582623725844167279/50000000000000000000)
  directionLo := (93170057174508594209/20000000000000000000)
  directionHi := (232925142936271485523/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree088.table
  base := (34817542976199681328011338631246709113201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-226037246503498790106689854077036000000000000)
      constant := (4848157088621860243734220826665189807908790049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree088.table
  base := (34817540532063809623303493192231322912043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-25187553551132480815152869919829000000000000)
      constant := (541717732108485609396590965664839695071247523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93170057174508594209/20000000000000000000)
  centralHi := (232925142936271485523/50000000000000000000)
  directionLo := (468519936873636500299/100000000000000000000)
  directionHi := (4685199368736365003/1000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree089.table
  base := (36396267896999947877024701372642993051797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-228607651557438262163949456122664750000000000)
      constant := (4961588563371709799451303389296290049269038453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree089.table
  base := (4549533222474291426089042418583749028873/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-12736987874179477199412628744773562500000000)
      constant := (277195295641352186055586716246397062015661362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468519936873636500299/100000000000000000000)
  centralHi := (4685199368736365003/1000000000000000000)
  directionLo := (18846978480324007761/4000000000000000000)
  directionHi := (235587231004050097013/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree090.table
  base := (38004006488617916916976140710246779239791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-25686450734597526024578784240921500000000000)
      constant := (564037656654804424581008285666655571680564551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree090.table
  base := (9501001163700158143968652262845015472637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-12880198972792713991248822529632625000000000)
      constant := (283605387885795281920278545068538036718118914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18846978480324007761/4000000000000000000)
  centralHi := (235587231004050097013/50000000000000000000)
  directionLo := (236907057751119444709/50000000000000000000)
  directionHi := (473814115502238889419/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree091.table
  base := (39640758579543178618352217953425918789581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-233748461665317206278468660213922250000000000)
      constant := (5192408127629212987531445209470156243741098669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree091.table
  base := (9910189247835903890461866654806696603197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-13023410071405950783085016314491687500000000)
      constant := (290089142757656185182259787458397950084226984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236907057751119444709/50000000000000000000)
  centralHi := (473814115502238889419/100000000000000000000)
  directionLo := (47643914453969385933/10000000000000000000)
  directionHi := (476439144539693859331/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree092.table
  base := (41306524023084663588915329107367853757281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-236318866719256678335728262259551000000000000)
      constant := (5309796216103030013903035329327912344357405969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree092.table
  base := (41306522647742639658786153529440282390159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-26333242340038375149842420198701500000000000)
      constant := (593293120462723080387528929005233676317847399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47643914453969385933/10000000000000000000)
  centralHi := (476439144539693859331/100000000000000000000)
  directionLo := (59881223691448873031/12500000000000000000)
  directionHi := (479049789531590984249/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree093.table
  base := (10750325673448931252748089891736428649247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-13271626209622008355165992461398875000000000)
      constant := (301583509717061930268512498956728402656631334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree093.table
  base := (43001301502900319276592833245350047482057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-26619664537264848733514807768419625000000000)
      constant := (606555280570106537711559833412651350539460077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59881223691448873031/12500000000000000000)
  centralHi := (479049789531590984249/100000000000000000000)
  directionLo := (48164628437350987303/10000000000000000000)
  directionHi := (481646284373509873031/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree094.table
  base := (11181273621103590495937512109919678943623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-120729838413567811225123733175404250000000000)
      constant := (2774264501846486469697603450255041440963162254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree094.table
  base := (4472509345332948267274170946559041733467/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-13453043367245661158593597669068875000000000)
      constant := (309982382900051936668780237837127959000782935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48164628437350987303/10000000000000000000)
  centralHi := (481646284373509873031/100000000000000000000)
  directionLo := (484228856690051323969/100000000000000000000)
  directionHi := (48422885669005132397/10000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree095.table
  base := (46477899303244204716616831400795459474679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1044)
      previous := (522)
      next := (522)
      square := (7472560268251145221274356380000000000000)
      linear := (-675983606318767574813038970627250000000000)
      constant := (15706021335630701086258764749871592729022111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree095.table
  base := (46477898410609588848997122959363770799641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (830284474250127246808261820000000000000)
      linear := (-75325509506143478949749537140875000000000)
      constant := (1754907413076995213199910755700081544237141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484228856690051323969/100000000000000000000)
  centralHi := (48422885669005132397/10000000000000000000)
  directionLo := (243398864033863449333/50000000000000000000)
  directionHi := (486797728067726898667/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree096.table
  base := (48259717071912653847947076435675624521931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-27400054103890507396085185604674000000000000)
      constant := (643615252229068069748873316154032900452417091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree096.table
  base := (6032464537401307141456002441381076651587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-13739465564472134742265985238787000000000000)
      constant := (323612855752457169185586032124226274684891628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243398864033863449333/50000000000000000000)
  centralHi := (486797728067726898667/100000000000000000000)
  directionLo := (244676557138422492323/50000000000000000000)
  directionHi := (489353114276844984647/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree097.table
  base := (10014109544690354310497283643441280764617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-249170891988954038622026272487694750000000000)
      constant := (5916519707172182716202292779610246758364953165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree097.table
  base := (25035273527315090886790258094084371647309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-13882676663085371534102179023646062500000000)
      constant := (330538585964587942290432604118070672520147299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244676557138422492323/50000000000000000000)
  centralHi := (489353114276844984647/100000000000000000000)
  directionLo := (245947612741511087779/50000000000000000000)
  directionHi := (491895225483022175559/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree098.table
  base := (25955195600327695091928368405391375400413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-125870648521446755339642937266661750000000000)
      constant := (3020910506654265259421815182853982570863441837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree098.table
  base := (51910390621801808259658331075438730980391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-28051775523397216651876745617010250000000000)
      constant := (675075957373700740014283017021037784227671151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245947612741511087779/50000000000000000000)
  centralHi := (491895225483022175559/100000000000000000000)
  directionLo := (494424266448906763841/100000000000000000000)
  directionHi := (247212133224453381921/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree099.table
  base := (13444811863668157554809687558899977427323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-14128427894268499040919193143275125000000000)
      constant := (342691177128441084894124042029100922374402206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree099.table
  base := (33612029346081206946002436773379728841/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-14169098860311845117774566593364187500000000)
      constant := (344611033910761781647244644754912026138499550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494424266448906763841/100000000000000000000)
  centralHi := (247212133224453381921/50000000000000000000)
  directionLo := (496940436726662315771/100000000000000000000)
  directionHi := (124235109181665578943/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree100.table
  base := (55677116443803769789965290415676055109867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-256882107150772454793805078624581000000000000)
      constant := (6296380232046927347602800322978936190551957883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree100.table
  base := (556771160103239988299948169902706644727/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-14312309958925081909610760378223250000000000)
      constant := (351757751629085832664013269202923347124822350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496940436726662315771/100000000000000000000)
  centralHi := (124235109181665578943/25000000000000000000)
  directionLo := (499443930841723408083/100000000000000000000)
  directionHi := (124860982710430852021/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree101.table
  base := (14400999533117331303130666063575435589039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-129726256102355963425532340335104875000000000)
      constant := (3212819072198948117440798538101057459754450422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree101.table
  base := (2880199887869995995565195424124009451797/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-14455521057538318701446954163082312500000000)
      constant := (358978131835652294542143726396748470507705920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499443930841723408083/100000000000000000000)
  centralHi := (124860982710430852021/25000000000000000000)
  directionLo := (125483734617075600007/25000000000000000000)
  directionHi := (501934938468302400029/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree102.table
  base := (116327915020170716744293640212873581193/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-14556828736591744383795793484213250000000000)
      constant := (364234162514792521716676729602402042067032288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree102.table
  base := (930623315091026158751734152666214264683/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-14598732156151555493283147947941375000000000)
      constant := (366272174525202837636001672484803980232493016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125483734617075600007/25000000000000000000)
  centralHi := (501934938468302400029/100000000000000000000)
  directionLo := (504413644597095369267/100000000000000000000)
  directionHi := (126103411149273842317/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree103.table
  base := (15386199872879503026921257999137631674701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-132296661156295435482791942380733625000000000)
      constant := (3344055287284007833014343862436972000544082098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree103.table
  base := (30772399605395073571769162194721136514209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-14741943254764792285119341732800437500000000)
      constant := (373639879693259055790452678201103052449598199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504413644597095369267/100000000000000000000)
  centralHi := (126103411149273842317/25000000000000000000)
  directionLo := (126720057423901712507/25000000000000000000)
  directionHi := (506880229695606850029/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree104.table
  base := (63558719114015990267426219443561808089623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-267163727366530343022843486807096000000000000)
      constant := (6821325092231587346783487113145062564483185127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree104.table
  base := (63558718871177409978574744478435549451221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-29770308706756058153911071035319000000000000)
      constant := (762162494672019047684226451161665920851890781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126720057423901712507/25000000000000000000)
  centralHi := (506880229695606850029/100000000000000000000)
  directionLo := (127333717465371647901/25000000000000000000)
  directionHi := (101866973972297318321/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree105.table
  base := (13120330267815410492576498522120102710351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-29970459157829979453344787650302750000000000)
      constant := (772873164244008915359772847014664656485933555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree105.table
  base := (65601651129031235436379355454148432700463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-30056730903982531737583458605037125000000000)
      constant := (777192554900426285552355067747355059790804643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127333717465371647901/25000000000000000000)
  centralHi := (101866973972297318321/20000000000000000000)
  directionLo := (127944434242311758973/25000000000000000000)
  directionHi := (511777736969247035893/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree106.table
  base := (8459199518845430379276494790652810064439/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-136152268737204643568681345449176750000000000)
      constant := (3545855366204856286126633471958715474284949244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree106.table
  base := (67673595969096838141986828522755049962177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-30343153101209005321255846174755250000000000)
      constant := (792369940066232847664928722464702381630095897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127944434242311758973/25000000000000000000)
  centralHi := (511777736969247035893/100000000000000000000)
  directionLo := (514208998810707440727/100000000000000000000)
  directionHi := (64276124851338430091/12500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree107.table
  base := (34887276767768910942618371592621745490071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-137437471264174379597311146471991125000000000)
      constant := (3614440927414250765428469582408856580394115679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree107.table
  base := (8721819172303588177110921400585620783371/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-15314787649217739452464116872236687500000000)
      constant := (403847325082382701972502690114291479672906474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514208998810707440727/100000000000000000000)
  centralHi := (64276124851338430091/12500000000000000000)
  directionLo := (258314409614744705659/50000000000000000000)
  directionHi := (516628819229489411319/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree108.table
  base := (35952261740957776263482946053580104249487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-15413630421238235069548994166089500000000000)
      constant := (409298435856396307227568926264807011384064807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree108.table
  base := (7190452334605499225066260635922396655883/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-15457998747830976244300310657095750000000000)
      constant := (411583342596031559171912003445599480651368815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258314409614744705659/50000000000000000000)
  centralHi := (516628819229489411319/100000000000000000000)
  directionLo := (519037358249868917933/100000000000000000000)
  directionHi := (259518679124934458967/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree109.table
  base := (74063505980167002227634054769774480887519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-280015752636227703309141497035239750000000000)
      constant := (7507180704137996993225665844570297284497299231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree109.table
  base := (4628969116418145527355005001308689022307/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-15601209846444213036136504441954812500000000)
      constant := (419393022572386986108575643285514532470641366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519037358249868917933/100000000000000000000)
  centralHi := (259518679124934458967/50000000000000000000)
  directionLo := (130358693050067889409/25000000000000000000)
  directionHi := (521434772200271557637/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree110.table
  base := (3812575051103133397388226292029896516759/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-141293078845083587683200549540434250000000000)
      constant := (3824154215485177132434977432301885830016999910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree110.table
  base := (15250300184098012354835488111923799221759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-31488841890114899655945396453627750000000000)
      constant := (854552730020066046119429010329567047439024995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130358693050067889409/25000000000000000000)
  centralHi := (521434772200271557637/100000000000000000000)
  directionLo := (104764242766336151087/20000000000000000000)
  directionHi := (130955303457920188859/25000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree111.table
  base := (784685086006549751439790536175569646933/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-15842031263561480412425594507027625000000000)
      constant := (432819723660535148629870655171495123924015650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree111.table
  base := (7846850851283996717414246119268355390437/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-15887632043670686619808892011672937500000000)
      constant := (435233369907775802397303382149150705210207535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104764242766336151087/20000000000000000000)
  centralHi := (130955303457920188859/25000000000000000000)
  directionLo := (105239366486242539699/20000000000000000000)
  directionHi := (4110912753368849207/781250000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree112.table
  base := (80714528710091481085060576167675393659053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-287726967798046119480920303172126000000000000)
      constant := (7934520488876817638195092395799479353998263197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree112.table
  base := (40357264317088156118176708322178619156757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-16030843142283923411645085796532000000000000)
      constant := (443264037264611070422921752826338606515589277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105239366486242539699/20000000000000000000)
  centralHi := (4110912753368849207/781250000000000000)
  directionLo := (528561773931096967541/100000000000000000000)
  directionHi := (264280886965548483771/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree113.table
  base := (82989561345454971526820468499649053428979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-290297372851985591538179905217754750000000000)
      constant := (8079604819915933124362847830144725801934502771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree113.table
  base := (20747390319957976552848548950225318506181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-16174054240897160203481279581391062500000000)
      constant := (451368367079696399206300009140317378691931432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528561773931096967541/100000000000000000000)
  centralHi := (264280886965548483771/50000000000000000000)
  directionLo := (265458090506643995471/50000000000000000000)
  directionHi := (530916181013287990943/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree114.table
  base := (85293606502626587815332744410307634920251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (116)
      previous := (58)
      next := (58)
      square := (830284474250127246808261820000000000000)
      linear := (-90140898093544187009984458991500000000000)
      constant := (2531858423820743909533497250522792009920251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree114.table
  base := (8529360644590438945421744872786121900957/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (58)
      previous := (29)
      next := (29)
      square := (415142237125063623404130910000000000000)
      linear := (-45200180995873675887306020405125000000000)
      constant := (1272981604854092556319964278193678656379785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265458090506643995471/50000000000000000000)
  centralHi := (530916181013287990943/100000000000000000000)
  directionLo := (106652038641983904977/20000000000000000000)
  directionHi := (266630096604959762443/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree115.table
  base := (43813332089084338224154566394570733752853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-147719091479932267826349554654506125000000000)
      constant := (4186865043049320107550306006686454874509894397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree115.table
  base := (43813332064571779837056660778693851321379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-16460476438123633787153667151109187500000000)
      constant := (467798014081917449785069910065993643901236569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106652038641983904977/20000000000000000000)
  centralHi := (266630096604959762443/50000000000000000000)
  directionLo := (535593946999802289307/100000000000000000000)
  directionHi := (133898486749950572327/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree116.table
  base := (5624295898076533016621165074063363931277/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-149004294006902003854979355677320500000000000)
      constant := (4261385510610890717690730127472029049051751784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree116.table
  base := (17997746865370998550063726733450438222869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-33207375073473741157979721871936500000000000)
      constant := (952246662535960333026381343904464150367278545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535593946999802289307/100000000000000000000)
  centralHi := (133898486749950572327/25000000000000000000)
  directionLo := (67239696987644200163/12500000000000000000)
  directionHi := (107583515180230720261/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree117.table
  base := (92379817073432581266399140760130466137089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-33397665896415942196357590377807750000000000)
      constant := (963681202706149767552550799452000313119239129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree117.table
  base := (46189908518408805402114166816007270330297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-16746898635350107370826054720827312500000000)
      constant := (484522310910114658458781178304341342850955967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67239696987644200163/12500000000000000000)
  centralHi := (107583515180230720261/20000000000000000000)
  directionLo := (540231210560737288091/100000000000000000000)
  directionHi := (135057802640184322023/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree118.table
  base := (23699978072213252346788247359471856088183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-151574699060841475912238957722949250000000000)
      constant := (4412404747746518568998959017318928800548513134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree118.table
  base := (1895998245144263764342168092653100970333/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-16890109733963344162662248505686375000000000)
      constant := (492994953007992735897659939086488390554130325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540231210560737288091/100000000000000000000)
  centralHi := (135057802640184322023/25000000000000000000)
  directionLo := (54253497883958227743/10000000000000000000)
  directionHi := (542534978839582277431/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree119.table
  base := (19449804002780983576041954576856460807601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-305719803175622423881737517491527250000000000)
      constant := (8977807034629712798420121917482448670663228245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree119.table
  base := (97249019986566075573289638128721345607621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-34066641665153161908996884581090875000000000)
      constant := (1003082515122696088220597324314243131350288681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54253497883958227743/10000000000000000000)
  centralHi := (542534978839582277431/100000000000000000000)
  directionLo := (544829005895439006297/100000000000000000000)
  directionHi := (272414502947719503149/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree120.table
  base := (99727140247312621342107391585984732086633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-34254467581062432882110791059684000000000000)
      constant := (1014680382417914465262635609142551738283274513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree120.table
  base := (99727140223691669122011963465244618828323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-34353063862379635492669272150809000000000000)
      constant := (1020322449139933524239370309526037994897024603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544829005895439006297/100000000000000000000)
  centralHi := (272414502947719503149/50000000000000000000)
  directionLo := (54711341426212411359/10000000000000000000)
  directionHi := (547113414262124113591/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree121.table
  base := (51117136494029849601376129686990335397139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-155430306641750683998128360791392375000000000)
      constant := (4643879358442143477198239833788140957127179611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree121.table
  base := (102234272967652365298910767164545826224333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-34639486059606109076341659720527125000000000)
      constant := (1037709708067359304964903208342919237602921713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54711341426212411359/10000000000000000000)
  centralHi := (547113414262124113591/100000000000000000000)
  directionLo := (137347080981473937223/25000000000000000000)
  directionHi := (549388323925895748893/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree122.table
  base := (1637037784927339231375859999623442939159/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-156715509168720420026758161814206750000000000)
      constant := (4722356429998147731916631609906734045185982912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree122.table
  base := (104770418217719921274056834282132371960809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-34925908256832582660014047290245250000000000)
      constant := (1055244291904710534735591574169925032371602049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137347080981473937223/25000000000000000000)
  centralHi := (549388323925895748893/100000000000000000000)
  directionLo := (551653852398994198591/100000000000000000000)
  directionHi := (8619591443734284353/1562500000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree123.table
  base := (53667787994286306332900004652584011589189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-17555634632854461783931995870780125000000000)
      constant := (533499215060848538020436791746513310605572229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree123.table
  base := (107335575973343297797834518122450347771903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-35212330454059056243686434859963375000000000)
      constant := (1072926200651788288382324158549960418319094483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551653852398994198591/100000000000000000000)
  centralHi := (8619591443734284353/1562500000000000000)
  directionLo := (553910114790475368207/100000000000000000000)
  directionHi := (34619382174404710513/6250000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree124.table
  base := (21985949249455211565646238483425272167927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-318571828445319784168035527719671000000000000)
      constant := (9762577750179751940767017599852404733867974115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree124.table
  base := (54964873117060596781818551724875946534997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-17749376325642764913679411214840750000000000)
      constant := (545377717154223848066707968641460208886633917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553910114790475368207/100000000000000000000)
  centralHi := (34619382174404710513/6250000000000000000)
  directionLo := (556157223874457933131/100000000000000000000)
  directionHi := (139039305968614483283/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree125.table
  base := (22510585802228175013541758497099513947631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (376884)
      previous := (188442)
      next := (188442)
      square := (2697594256838663424880042653180000000000000)
      linear := (-321142233499259256225295129765299750000000000)
      constant := (9923488497248693245712127565170386975173015595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree125.table
  base := (56276464499889297059373162785777920042311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-17892587424256001705515604999699812500000000)
      constant := (554365996437294738885717808407409664584493021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556157223874457933131/100000000000000000000)
  centralHi := (139039305968614483283/25000000000000000000)
  directionLo := (279197645077949324719/50000000000000000000)
  directionHi := (558395290155898649439/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree126.table
  base := (115205124279960126296517410709121059278389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-35968070950355414253617192423436500000000000)
      constant := (1120635345811269473039578312965135061774498429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree126.table
  base := (1800080066721043059192998206728128482503/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-18035798522869238497351798784558875000000000)
      constant := (563427938175076358414888339556892791401749656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279197645077949324719/50000000000000000000)
  centralHi := (558395290155898649439/100000000000000000000)
  directionLo := (112124884386800874881/20000000000000000000)
  directionHi := (280312210967002187203/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree127.table
  base := (58943166026810613506980373072535010957681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-163141521803569100169907166928278625000000000)
      constant := (5124633297668791094328243536318160639273380569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree127.table
  base := (4715453281805845139652870066492942495209/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (41876)
      previous := (20938)
      next := (20938)
      square := (299732695204295936097782517020000000000000)
      linear := (-36358019242964950578375985138835875000000000)
      constant := (1145127084735108695729150461073812484730198725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112124884386800874881/20000000000000000000)
  centralHi := (280312210967002187203/50000000000000000000)
  directionLo := (281422362681691878657/50000000000000000000)
  directionHi := (112568945072676751463/20000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree128.table
  base := (30149138083022672127477267195358520682331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (188442)
      previous := (94221)
      next := (94221)
      square := (1348797128419331712440021326590000000000000)
      linear := (-164426724330538836198536967951093000000000000)
      constant := (5207066973178527617396881420106003667393786838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree128.table
  base := (1884321130074559261543008489947178807711/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-18322220720095712081024186354277000000000000)
      constant := (581772809014727819267031420984875809586677472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell039.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281422362681691878657/50000000000000000000)
  centralHi := (112568945072676751463/20000000000000000000)
  directionLo := (565056304513036301533/100000000000000000000)
  directionHi := (282528152256518150767/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 869
  qDenominator := 1824
  table := BinomialMassData.Q869_1824.Degree129.table
  base := (30833946278850275973018449793698576968297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-18412436317500952469685196552656375000000000)
      constant := (587795564742219460598610362488978089367985434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q869_1824.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 581
  qDenominator := 1216
  table := BinomialMassData.Q581_1216.Degree129.table
  base := (12333578510908104724518681321097223456723/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (20938)
      previous := (10469)
      next := (10469)
      square := (149866347602147968048891258510000000000000)
      linear := (-18465431818708948872860380139136062500000000)
      constant := (591055738116607115040231841698797421444853765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q581_1216.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell039.Kernel129
