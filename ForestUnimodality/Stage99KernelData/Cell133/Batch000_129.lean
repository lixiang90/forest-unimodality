import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell133.Parameters
import ForestUnimodality.BinomialMassData.Q28_53.Batch000_049
import ForestUnimodality.BinomialMassData.Q28_53.Batch050_099
import ForestUnimodality.BinomialMassData.Q28_53.Batch100_149
import ForestUnimodality.BinomialMassData.Q95449_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95449_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q95449_180624.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree000.table
  base := (1429248583243929525160353941/25000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-370248457509515149777001852500000000000000)
      constant := (30300069964771305933399503549200000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree000.table
  base := (1429248583243929525160353941/25000000000000000000000000)
  polynomial :=
    { denominator := 602080000000000000000000000000000000000000000
      center := (3913409)
      previous := (0)
      next := (3492175)
      square := (90524293089007216726038507088000000000000000)
      linear := (-420602247730809210146674104440000000000000000)
      constant := (34420879479980203540341836031891200000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree001.table
  base := (85977279111322588779269496888829105022489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-454445913212817105275576068500000000000000)
      constant := (18445026967640250171596380338431770264767668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree001.table
  base := (343849682345719352787151140304438906581231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-329900118736680362377712838560574000000000000000)
      constant := (13387077913096076059966248330476165449775921114672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (1996761977086751159/4000000000000000000)
  directionHi := (1559970294599024343/3125000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree002.table
  base := (216097532795828289678336649057109388414853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-538643368916119060774150284500000000000000)
      constant := (11933338504969800445318488812026797585987209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree002.table
  base := (43206208156699861085407142863005283779089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-391035401173373639471700924383988000000000000000)
      constant := (8660008254033031781972119870753543441839592685840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1996761977086751159/4000000000000000000)
  centralHi := (1559970294599024343/3125000000000000000)
  directionLo := (70596196720674968671/100000000000000000000)
  directionHi := (2206131147521092771/3125000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree003.table
  base := (142783842404385110629976224965099110574649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-622840824619421016272724500500000000000000)
      constant := (8354520059685530089314938165150252860456397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree003.table
  base := (71363456444905023913853278843896094376493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-50241187067785212951743223356378000000000000000)
      constant := (673619669866744228108157717597447226631224457248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70596196720674968671/100000000000000000000)
  centralHi := (2206131147521092771/3125000000000000000)
  directionLo := (43231164936699192541/50000000000000000000)
  directionHi := (86462329873398385083/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree004.table
  base := (99386194665565946716814118650681401015727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-707038280322722971771298716500000000000000)
      constant := (6405733549701510927061050776486114253833531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree004.table
  base := (49670801061913560313406482673803049919561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-513305966046760193659677096030816000000000000000)
      constant := (4648516168805231040474852303853175889773754863264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43231164936699192541/50000000000000000000)
  centralHi := (86462329873398385083/100000000000000000000)
  directionLo := (1996761977086751159/2000000000000000000)
  directionHi := (99838098854337557951/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree005.table
  base := (907323417914849771137365526303762113651/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-791235736026024927269872932500000000000000)
      constant := (5381087019270053697420188981527951361880240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree005.table
  base := (72551827154756929035363865238001690207197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-574441248483453470753665181854230000000000000000)
      constant := (3905240243855765881995906323167902770692751947664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1996761977086751159/2000000000000000000)
  centralHi := (99838098854337557951/100000000000000000000)
  directionLo := (55811193945660663499/50000000000000000000)
  directionHi := (111622387891321326999/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree006.table
  base := (3446327656140115874508881014915511059453/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-875433191729326882768447148500000000000000)
      constant := (4896773749313662237693299328648353378416144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree006.table
  base := (55115037655795665160758343049179751685611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-70619614546682971983072585297516000000000000000)
      constant := (394900805841512048357737898773417778753595963248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55811193945660663499/50000000000000000000)
  centralHi := (111622387891321326999/100000000000000000000)
  directionLo := (30569049885334101599/25000000000000000000)
  directionHi := (122276199541336406397/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree007.table
  base := (10773603463374173319154018365782913069063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-959630647432628838267021364500000000000000)
      constant := (4743025675449100419666581615545977570641356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree007.table
  base := (8614735362718804195352247564963578307/2000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-696711813356840024941641353501058000000000000000)
      constant := (3442858459943770347191817562453320344551599920000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30569049885334101599/25000000000000000000)
  centralHi := (122276199541336406397/100000000000000000000)
  directionLo := (132073390469029896871/100000000000000000000)
  directionHi := (16509173808628737109/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree008.table
  base := (27412322418290066275397216971281230471/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-1043828103135930793765595580500000000000000)
      constant := (4804303620443602658231309256347381518703750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree008.table
  base := (4281047007395418721212954336545038098977/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-757847095793533302035629439324472000000000000000)
      constant := (3487647210795985483898362384618253078548715288192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132073390469029896871/100000000000000000000)
  centralHi := (16509173808628737109/12500000000000000000)
  directionLo := (141192393441349937343/100000000000000000000)
  directionHi := (2206131147521092771/1562500000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree009.table
  base := (2743951233104902005874255246280191255013/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-1128025558839232749264169796500000000000000)
      constant := (5016228607506772313664065238528501365156890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree009.table
  base := (13712500238471460320434509297867991901207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-90998042025580731014401947238654000000000000000)
      constant := (404640244374195379424141573195184807507077689952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141192393441349937343/100000000000000000000)
  centralHi := (2206131147521092771/1562500000000000000)
  directionLo := (5990285931260253477/4000000000000000000)
  directionHi := (74878574140753168463/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree010.table
  base := (10964125930450495547061484470126375302147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-1212223014542534704762744012500000000000000)
      constant := (5342310671029393653187846053833395782027582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree010.table
  base := (10957742013507453785110167501334830026543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-880117660666919856223605610971300000000000000000)
      constant := (3878731521455142132248357049109123346292293006432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5990285931260253477/4000000000000000000)
  centralHi := (74878574140753168463/50000000000000000000)
  directionLo := (157857894820376962999/100000000000000000000)
  directionHi := (157857894820376963/100000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree011.table
  base := (4332924972911981079552097735107439371013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-1296420470245836660261318228500000000000000)
      constant := (5761353959810626380297144577842777146654756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree011.table
  base := (4330048853171391343385256715040935094999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-941252943103613133317593696794714000000000000000)
      constant := (4183180197347992286768823667232677576730432668352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157857894820376962999/100000000000000000000)
  centralHi := (157857894820376963/100000000000000000)
  directionLo := (165562756841124494497/100000000000000000000)
  directionHi := (82781378420562247249/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree012.table
  base := (536383823781496924918707144707753539589/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-1380617925949138615759892444500000000000000)
      constant := (6260624649926593474766310398737773439955425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree012.table
  base := (13399061360281314916377057545410422834077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-111376469504478490045731309179792000000000000000)
      constant := (505096878790523705734865299343696022397581669136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165562756841124494497/100000000000000000000)
  centralHi := (82781378420562247249/50000000000000000000)
  directionLo := (34584931949359354033/20000000000000000000)
  directionHi := (86462329873398385083/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree013.table
  base := (2502797116217066689674623040648198396913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-1464815381652440571258466660500000000000000)
      constant := (6832132964628130236861119506617418060145556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree013.table
  base := (5000723661903499065187573793674825835339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-1063523507976999687505569868441542000000000000000)
      constant := (4961011307123073657993403423689383149456647674336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34584931949359354033/20000000000000000000)
  centralHi := (86462329873398385083/50000000000000000000)
  directionLo := (17998569233207831513/10000000000000000000)
  directionHi := (179985692332078315131/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree014.table
  base := (7036883675206031396962605679772151969501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-1549012837355742526757040876500000000000000)
      constant := (7470600378061212203674345929027924054383553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree014.table
  base := (878478446566577629238142186898282120257/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-1124658790413692964599557954264956000000000000000)
      constant := (5424769346692962451691884113385707037710567827072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17998569233207831513/10000000000000000000)
  centralHi := (179985692332078315131/100000000000000000000)
  directionLo := (186779980029899549201/100000000000000000000)
  directionHi := (93389990014949774601/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree015.table
  base := (883425209578723865484943467397441068831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-1633210293059044482255615092500000000000000)
      constant := (8172340465810013196558218668860321883240215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree015.table
  base := (2204343332812830060384166660945421361613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-131754896983376249077060671120930000000000000000)
      constant := (659385729598509872124146217382582361466279361568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186779980029899549201/100000000000000000000)
  centralHi := (93389990014949774601/50000000000000000000)
  directionLo := (38667129417985914929/20000000000000000000)
  directionHi := (96667823544964787323/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree016.table
  base := (1050327320803903328656102557224319155301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-1717407748762346437754189308500000000000000)
      constant := (8934636397984402349195788759065777830461906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree016.table
  base := (2092785655426479633692406084097173409063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-1246929355287079518787534125911784000000000000000)
      constant := (6488146654679671077828107279849887152015620801456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38667129417985914929/20000000000000000000)
  centralHi := (96667823544964787323/50000000000000000000)
  directionLo := (1996761977086751159/1000000000000000000)
  directionHi := (199676197708675115901/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree017.table
  base := (23935078132505527335339989457952664197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-1801605204465648393252763524500000000000000)
      constant := (9755389411679949797993473580882542982404882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree017.table
  base := (2026843762365746391527486125266399919/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-1308064637723772795881522211735198000000000000000)
      constant := (7084271558755445437166355660605132091112809882560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1996761977086751159/1000000000000000000)
  centralHi := (199676197708675115901/100000000000000000000)
  directionLo := (51455378379661411983/25000000000000000000)
  directionHi := (205821513518645647933/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree018.table
  base := (-354598530133858925513466866688553689047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-1885802660168950348751337740500000000000000)
      constant := (10632915949042325604156696892327533272402545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree018.table
  base := (-444954776812596652212470855038937379303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-152133324462274008108390033062068000000000000000)
      constant := (857958266752042315364662100473753396947806693184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51455378379661411983/25000000000000000000)
  centralHi := (205821513518645647933/100000000000000000000)
  directionLo := (42357718032404981203/20000000000000000000)
  directionHi := (6618393442563278313/3125000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree019.table
  base := (-1694070563711322064237447758134078016597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-1970000115872252304249911956500000000000000)
      constant := (11565827020615470479514586635637787730240718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree019.table
  base := (-848621736629414792947227590727313516821/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-1430335202597159350069498383382026000000000000000)
      constant := (8399197011353792234264762434774450891783740588992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42357718032404981203/20000000000000000000)
  centralHi := (6618393442563278313/3125000000000000000)
  directionLo := (43518418362128131187/20000000000000000000)
  directionHi := (3399876434541260249/1562500000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree020.table
  base := (-2409816249055737755689022194800734175011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-2054197571575554259748486172500000000000000)
      constant := (12552953593521213206710862647351122177448834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree020.table
  base := (-4825522722194476561219402684332527986523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-1491470485033852627163486469205440000000000000000)
      constant := (9116140828900625921416101404387235872036963435024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43518418362128131187/20000000000000000000)
  centralHi := (3399876434541260249/1562500000000000000)
  directionLo := (223244775782642653997/100000000000000000000)
  directionHi := (111622387891321326999/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree021.table
  base := (-6086287038525358762690402302932433923719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-2138395027278856215247060388500000000000000)
      constant := (13593298193142706576465602995944581002042893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree021.table
  base := (-3045873119420936900190383587328458736419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-172511751941171767139719395003206000000000000000)
      constant := (1096859088969349777850885351192151385708471248416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223244775782642653997/100000000000000000000)
  centralHi := (111622387891321326999/50000000000000000000)
  directionLo := (2287578226202428943/1000000000000000000)
  directionHi := (228757822620242894301/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree022.table
  base := (-720431255560381144446268745651872054419/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-2222592482982158170745634604500000000000000)
      constant := (14686001805712156157990119616804507811157930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree022.table
  base := (-7209365038319701067688228596982881815839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-1613741049907239181351462640852268000000000000000)
      constant := (10665346375492648139743009462029845872392825946832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2287578226202428943/1000000000000000000)
  centralHi := (228757822620242894301/100000000000000000000)
  directionLo := (234141096148597184291/100000000000000000000)
  directionHi := (58535274037149296073/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree023.table
  base := (-8187754673442964989765632833741077828097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-2306789938685460126244208820500000000000000)
      constant := (15830320013152466985331663661811722875110859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree023.table
  base := (-256013264206771327253045984688464145877/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-1674876332343932458445450726675682000000000000000)
      constant := (11496444188307567547035094844361276075516608517632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234141096148597184291/100000000000000000000)
  centralHi := (58535274037149296073/25000000000000000000)
  directionLo := (14962709428538861569/6250000000000000000)
  directionHi := (47880670171324357021/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree024.table
  base := (-4524418749277237163450005666367691439633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-2390987394388762081742783036500000000000000)
      constant := (17025604937818521347290294167365024707398902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree024.table
  base := (-72425185439757298304679549005497669601/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-192890179420069526171048756944344000000000000000)
      constant := (1373839439792573669956065343203516342239384054000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14962709428538861569/6250000000000000000)
  centralHi := (47880670171324357021/20000000000000000000)
  directionLo := (30569049885334101599/12500000000000000000)
  directionHi := (244552399082672812793/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree025.table
  base := (-1224778977021497019238300017503994377867/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-2475184850092064037241357252500000000000000)
      constant := (18271291028092936498869860542578306383784392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree025.table
  base := (-9802206432942083745875464199438361631479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-1797146897217319012633426898322510000000000000000)
      constant := (13269268170589622469638053984008724651027932003152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30569049885334101599/12500000000000000000)
  centralHi := (244552399082672812793/100000000000000000000)
  directionLo := (1996761977086751159/800000000000000000)
  directionHi := (62398811783960973719/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree026.table
  base := (-2089054558715335263359113787491235167777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-2559382305795365992739931468500000000000000)
      constant := (19566883520109808530231791994314822680539095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree026.table
  base := (-10448933669230340713842594136210458927833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-1858282179654012289727414984145924000000000000000)
      constant := (14210224701984370607120216938070644750189866640304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1996761977086751159/800000000000000000)
  centralHi := (62398811783960973719/25000000000000000000)
  directionLo := (15908637945571020723/6250000000000000000)
  directionHi := (254538207129136331569/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree027.table
  base := (-10998140671943479253331234176902814852417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-2643579761498667948238505684500000000000000)
      constant := (20911948861086867506174611550624150812821899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree027.table
  base := (-5500754648469624896980230794748737185027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-213268606898967285202378118885482000000000000000)
      constant := (1687456651852130971794131921365701247982073002528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15908637945571020723/6250000000000000000)
  centralHi := (254538207129136331569/100000000000000000000)
  directionLo := (259386989620195155247/100000000000000000000)
  directionHi := (16211686851262197203/6250000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree028.table
  base := (-11464013095055549780556292964316386679469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-2727777217201969903737079900500000000000000)
      constant := (22306106635903605691395045664891231505988143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree028.table
  base := (-11467110033960520423723165185441169779289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-1980552744527398843915391155792752000000000000000)
      constant := (16199647555408150324000685089707851193904354880432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259386989620195155247/100000000000000000000)
  centralHi := (16211686851262197203/6250000000000000000)
  directionLo := (132073390469029896871/50000000000000000000)
  directionHi := (264146780938059793743/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree029.table
  base := (-5924597454557667121702354064398776935119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-2811974672905271859235654116500000000000000)
      constant := (23749022687711293429611594307173729644877386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree029.table
  base := (-11852039736172542965959464023602065472963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-2041688026964092121009379241616166000000000000000)
      constant := (17247595240508815345549951410413673499540456121744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132073390469029896871/50000000000000000000)
  centralHi := (264146780938059793743/100000000000000000000)
  directionLo := (26882230818079713157/10000000000000000000)
  directionHi := (268822308180797131571/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree030.table
  base := (-1215922957748064826697465065266105081277/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-2896172128608573814734228332500000000000000)
      constant := (25240403212951966492694054415408964306923190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree030.table
  base := (-1520230104713806000979419049885605859833/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-233647034377865044233707480826620000000000000000)
      constant := (2036748854265603015067382291833412617278187250048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26882230818079713157/10000000000000000000)
  centralHi := (268822308180797131571/100000000000000000000)
  directionLo := (136708947102378405387/50000000000000000000)
  directionHi := (10936715768190272431/4000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree031.table
  base := (-12398995297635571720961840034286152910657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-2980369584311875770232802548500000000000000)
      constant := (26779989667158968647548552856182833895735179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree031.table
  base := (-620069524481961260947004929337413613187/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-2163958591837478675197355413262994000000000000000)
      constant := (19448893260849251640331135743485938542545090189120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136708947102378405387/50000000000000000000)
  centralHi := (10936715768190272431/4000000000000000000)
  directionLo := (69484376106735186873/25000000000000000000)
  directionHi := (277937504426940747493/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree032.table
  base := (-6286394107837782292460205456348219951079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-3064567040015177725731376764500000000000000)
      constant := (28367554354589240515258720493627088685185626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree032.table
  base := (-6287491896086053341232672889747530310609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-2225093874274171952291343499086408000000000000000)
      constant := (20601890712872754000551827993673403128285214553184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69484376106735186873/25000000000000000000)
  centralHi := (277937504426940747493/100000000000000000000)
  directionLo := (141192393441349937343/50000000000000000000)
  directionHi := (282384786882699874687/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree033.table
  base := (-12684394656761753717189996017662150609867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-3148764495718479681229950980500000000000000)
      constant := (30002896600009242372332556793063906017677049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree033.table
  base := (-6343203019580538792256201075240737737499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-254025461856762803265036842767758000000000000000)
      constant := (2421065157020408072130926458292487291546693749536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141192393441349937343/50000000000000000000)
  centralHi := (282384786882699874687/100000000000000000000)
  directionLo := (143381553344999672251/50000000000000000000)
  directionHi := (286763106689999344503/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree034.table
  base := (-1273715394473505896224655912309787932871/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-3232961951421781636728525196500000000000000)
      constant := (31685839419255405467012835674475812395578370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree034.table
  base := (-6369497774246975886530853548443957135849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-2347364439147558506479319670733236000000000000000)
      constant := (23011851926971681698164933313713831550361418755424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143381553344999672251/50000000000000000000)
  centralHi := (286763106689999344503/100000000000000000000)
  directionLo := (36384446980778250351/12500000000000000000)
  directionHi := (291075575846226002809/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree035.table
  base := (-397937910086093484467374641341937034477/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-3317159407125083592227099412500000000000000)
      constant := (33416226619040275706607665058284074789527008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree035.table
  base := (-3183924597688062332660707265831314938759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-2408499721584251783573307756556650000000000000000)
      constant := (24268573910322552536550220736750249541567358415168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36384446980778250351/12500000000000000000)
  centralHi := (291075575846226002809/100000000000000000000)
  directionLo := (36915634888452960297/12500000000000000000)
  directionHi := (295325079107623682377/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree036.table
  base := (-12677574681714556184722319774648781667143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-3401356862828385547725673628500000000000000)
      constant := (35193920267346523834310631059943614571641421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree036.table
  base := (-2535823224670584150860605362493833152853/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-274403889335660562296366204708896000000000000000)
      constant := (2839961363749635542283660549724887809204224434480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36915634888452960297/12500000000000000000)
  centralHi := (295325079107623682377/100000000000000000000)
  directionLo := (5990285931260253477/2000000000000000000)
  directionHi := (299514296563012673851/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree037.table
  base := (-12570138237645193434397176579248822430613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-3485554318531687503224247844500000000000000)
      constant := (37018798484524483507498597623299812411177511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree037.table
  base := (-12571547471813048130360109895233114683061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-2530770286457638337761283928203478000000000000000)
      constant := (26884998578579652876569424455149999846812686256368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5990285931260253477/2000000000000000000)
  centralHi := (299514296563012673851/100000000000000000000)
  directionLo := (30364572340368705613/10000000000000000000)
  directionHi := (303645723403687056131/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree038.table
  base := (-12413736962991346450111033743956625882787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-3569751774234989458722822060500000000000000)
      constant := (38890753512434599236670649583570298828212289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree038.table
  base := (-12415024763385995666955453493617751850919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-2591905568894331614855272014026892000000000000000)
      constant := (28244534635273777641715886448692183421401756193872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30364572340368705613/10000000000000000000)
  centralHi := (303645723403687056131/100000000000000000000)
  directionLo := (61544337460747936729/20000000000000000000)
  directionHi := (153860843651869841823/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree039.table
  base := (-12210169462735758066315791512897836607177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-3653949229938291414221396276500000000000000)
      constant := (40809690025012785651600836227816414659819619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree039.table
  base := (-763209112772652699945423355814071843851/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-294782316814558321327695566650034000000000000000)
      constant := (3293132364109542200475416706723986955215275974912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61544337460747936729/20000000000000000000)
  centralHi := (153860843651869841823/50000000000000000000)
  directionLo := (311744363754619731237/100000000000000000000)
  directionHi := (155872181877309865619/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree040.table
  base := (-2392205538051327022276423781101271712753/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-3738146685641593369719970492500000000000000)
      constant := (42775523648729997790385512098008162996120455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree040.table
  base := (-1495262724522192431215001901040147879159/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-2714176133767718169043248185673720000000000000000)
      constant := (31065907285563170613737051770049197457425033271936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311744363754619731237/100000000000000000000)
  centralHi := (155872181877309865619/50000000000000000000)
  directionLo := (157857894820376962999/50000000000000000000)
  directionHi := (315715789640753925999/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree041.table
  base := (-11667721416160743532601660337843978734251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-3822344141344895325218544708500000000000000)
      constant := (44788179665744077057818220040094269127084697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree041.table
  base := (-5834350901891129250919265461636936569137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-2775311416204411446137236271497134000000000000000)
      constant := (32527628450173788959877274694889974714352020566112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157857894820376962999/50000000000000000000)
  centralHi := (315715789640753925999/100000000000000000000)
  directionLo := (499434180151113703/156250000000000000)
  directionHi := (319637875296712769921/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree042.table
  base := (-11331499693656120758485709858924469285169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-3906541597048197280717118924500000000000000)
      constant := (46847591876234997470187861469477003127886043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree042.table
  base := (-11332394220017120896137194059497705048999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-315160744293456080359024928591172000000000000000)
      constant := (3780367415723315562878290197245764864383100642768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499434180151113703/156250000000000000)
  centralHi := (319637875296712769921/100000000000000000000)
  directionLo := (323512415248486287847/100000000000000000000)
  directionHi := (40439051906060785981/12500000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree043.table
  base := (-10953469704352244366212411991523484952459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-3990739052751499236215693140500000000000000)
      constant := (48953701599577456715903994726449255297519673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree043.table
  base := (-5477142805008626830538571366956873541283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-2897581981077798000325212443143962000000000000000)
      constant := (35552899586788257921544256148822774680402181547808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323512415248486287847/100000000000000000000)
  centralHi := (40439051906060785981/12500000000000000000)
  directionLo := (5114704653285191703/1562500000000000000)
  directionHi := (327341097810252268993/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree044.table
  base := (-421384532685623521447440566369839594243/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-4074936508454801191714267356500000000000000)
      constant := (51106456796720206689905194697559962537628025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree044.table
  base := (-10535357268415084078442136370858907370009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-2958717263514491277419200528967376000000000000000)
      constant := (37116369232747003079637742036360962892337492303792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5114704653285191703/1562500000000000000)
  centralHi := (327341097810252268993/100000000000000000000)
  directionLo := (165562756841124494497/50000000000000000000)
  directionHi := (66225102736449797799/20000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree045.table
  base := (-2518950412184074584900332572138365896197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-4159133964158103147212841572500000000000000)
      constant := (53305811298477344623918136244706666430006236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree045.table
  base := (-10076479778011827945365401112444721009693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-335539171772353839390354290532310000000000000000)
      constant := (4301520242836730627925439219576099092358836673776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165562756841124494497/50000000000000000000)
  centralHi := (66225102736449797799/20000000000000000000)
  directionLo := (83716790918490995249/25000000000000000000)
  directionHi := (334867163673963980997/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree046.table
  base := (-4788903938246025284778319620881121391987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-4243331419861405102711415788500000000000000)
      constant := (55551724126449178727408610588186601132449378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree046.table
  base := (-2394606455150108516087244463921182125501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-3080987828387877831607176700614204000000000000000)
      constant := (40344808717820351515118722569043358490598508284352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83716790918490995249/25000000000000000000)
  centralHi := (334867163673963980997/100000000000000000000)
  directionLo := (338567465658999050869/100000000000000000000)
  directionHi := (33856746565899905087/10000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree047.table
  base := (-2260329630334942029707340083849108421323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-4327528875564707058209990004500000000000000)
      constant := (57844158895026317060559414504223989014679524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree047.table
  base := (-4520940728925950835052222665489138339/5000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-3142123110824571108701164786437618000000000000000)
      constant := (42009722434826035744497924901060637074955653664000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338567465658999050869/100000000000000000000)
  centralHi := (33856746565899905087/10000000000000000000)
  directionLo := (85556940213254186513/25000000000000000000)
  directionHi := (342227760853016746053/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree048.table
  base := (-1058367923803188080636363339847003885923/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-4411726331268009013708564220500000000000000)
      constant := (60183083284430018779513963095904870352368648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree048.table
  base := (-4233728035937001401779583582378277655707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-355917599251251598421683652473448000000000000000)
      constant := (4856488876871491294579989012560559949564537398048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85556940213254186513/25000000000000000000)
  centralHi := (342227760853016746053/100000000000000000000)
  directionLo := (34584931949359354033/10000000000000000000)
  directionHi := (345849319493593540331/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree049.table
  base := (-7855224344542227001927037461764359772163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-4495923786971310969207138436500000000000000)
      constant := (62568468576038256641032211132526488932075361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree049.table
  base := (-1963922782645188730405151387792027663333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-3264393675697957662889140958084446000000000000000)
      constant := (45440820257025102418098586619857761969128095457216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34584931949359354033/10000000000000000000)
  centralHi := (345849319493593540331/100000000000000000000)
  directionLo := (13977333839607258113/4000000000000000000)
  directionHi := (174716672995090726413/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree050.table
  base := (-7206643034294274753507514462888673841919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-4580121242674612924705712652500000000000000)
      constant := (65000289242369000648213161233466900286378293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree050.table
  base := (-7207067921831854893706139209003361044049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-3325528958134650939983129043907860000000000000000)
      constant := (47206965013825605259130211118780107832848074699312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13977333839607258113/4000000000000000000)
  centralHi := (174716672995090726413/50000000000000000000)
  directionLo := (176490491801687421679/50000000000000000000)
  directionHi := (352980983603374843359/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree051.table
  base := (-1304325546117061132581523855261787056433/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-4664318698377914880204286868500000000000000)
      constant := (67478522585064356939613823476355626430045255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree051.table
  base := (-3261007190976374549239878084434646400453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-376296026730149357453013014414586000000000000000)
      constant := (5445201966476482185825301813415720138452056660192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176490491801687421679/50000000000000000000)
  centralHi := (352980983603374843359/100000000000000000000)
  directionLo := (44561664838127348701/12500000000000000000)
  directionHi := (356493318705018789609/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree052.table
  base := (-5800559359115120025495710516056844445529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-4748516154081216835702861084500000000000000)
      constant := (70003148415062236099579674854648987244386963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree052.table
  base := (-2900455564167168971957539421726338442093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-3447799523008037494171105215554688000000000000000)
      constant := (50840363666953919876994368952337356386070277830368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44561664838127348701/12500000000000000000)
  centralHi := (356493318705018789609/100000000000000000000)
  directionLo := (359971384664156630261/100000000000000000000)
  directionHi := (179985692332078315131/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree053.table
  base := (-5043776834763313961602303759929119521711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-4832713609784518791201435300500000000000000)
      constant := (72574148769874019533733198042723756665349317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree053.table
  base := (-630512098999959939874168339815193788043/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-3508934805444730771265093301378102000000000000000)
      constant := (52707589891700795289001905617180854312537400070272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359971384664156630261/100000000000000000000)
  centralHi := (179985692332078315131/50000000000000000000)
  directionLo := (11356755168694200579/3125000000000000000)
  directionHi := (363416165398214418529/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree054.table
  base := (-850316355948191986257876564521428674603/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-4916911065487820746700009516500000000000000)
      constant := (75191507663522520401691107898401821401230205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree054.table
  base := (-531484091753123104297982526850306066759/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-396674454209047116484342376355724000000000000000)
      constant := (6067609419810088957438157251009311116684902104704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11356755168694200579/3125000000000000000)
  centralHi := (363416165398214418529/100000000000000000000)
  directionLo := (366828598624009219189/100000000000000000000)
  directionHi := (36682859862400921919/10000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree055.table
  base := (-428030337369782966416279477170356569471/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-5001108521191122702198583732500000000000000)
      constant := (77855210865247497796224420151679768814544296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree055.table
  base := (-1712253609633167532012677204771803666581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-3631205370318117325453069473024930000000000000000)
      constant := (56543038005793735157149096230027909022408703692256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366828598624009219189/100000000000000000000)
  centralHi := (36682859862400921919/10000000000000000000)
  directionLo := (370209578839022718793/100000000000000000000)
  directionHi := (185104789419511359397/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree056.table
  base := (-256199867697423749283934839968949049823/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-5085305976894424657697157948500000000000000)
      constant := (80565245703567324074384067062816457003593810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree056.table
  base := (-320279888969950255432147578246831386839/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-3692340652754810602547057558848344000000000000000)
      constant := (58511240384414566847646964594017484334202441558656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370209578839022718793/100000000000000000000)
  centralHi := (185104789419511359397/50000000000000000000)
  directionLo := (186779980029899549201/50000000000000000000)
  directionHi := (373559960059799098403/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree057.table
  base := (-333012530596316585622376621933416048263/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-5169503432597726613195732164500000000000000)
      constant := (83321600892704786045418405017187644747210305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree057.table
  base := (-832640574123316370238117800960392465197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-417052881687944875515671738296862000000000000000)
      constant := (6723675969950149715925278167665009977544669501408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186779980029899549201/50000000000000000000)
  centralHi := (373559960059799098403/100000000000000000000)
  directionLo := (376880558341221439581/100000000000000000000)
  directionHi := (188440279170610719791/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree058.table
  base := (-146724864675891453365074224252915123771/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-5253700888301028568694306380500000000000000)
      constant := (86124266378750728376154524862572977492200685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree058.table
  base := (-146764567875807190824284960854875732763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-3814611217628197156735033730495172000000000000000)
      constant := (62548560750177454536206863480326656355812367920720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376880558341221439581/100000000000000000000)
  centralHi := (188440279170610719791/50000000000000000000)
  directionLo := (190086077048861561813/50000000000000000000)
  directionHi := (380172154097723123627/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree059.table
  base := (232147284536310626038880308352363968291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-5337898344004330524192880596500000000000000)
      constant := (88973233203258472136748417314342675290319423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree059.table
  base := (57991739468273651157991961236110635297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-3875746500064890433829021816318586000000000000000)
      constant := (64617664949873537124310938975535288870276182299456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190086077048861561813/50000000000000000000)
  centralHi := (380172154097723123627/100000000000000000000)
  directionLo := (191717747122570173667/50000000000000000000)
  directionHi := (76687098849028069467/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree060.table
  base := (30802538237447333470610100578093479941/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-5422095799707632479691454812500000000000000)
      constant := (91868493382240822474382289613225558177474920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree060.table
  base := (1231937758342750898729284751245710219597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-437431309166842634547001100238000000000000000000)
      constant := (7413376726559667511347425934865338122184006228496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191717747122570173667/50000000000000000000)
  centralHi := (76687098849028069467/20000000000000000000)
  directionLo := (38667129417985914929/10000000000000000000)
  directionHi := (386671294179859149291/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree061.table
  base := (566526032534571432181988938292588752277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-5506293255410934435190029028500000000000000)
      constant := (94810039798785328116487569812918028815482724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree061.table
  base := (2265955423654488112272126882511116947503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-3998017064938276988016997987965414000000000000000)
      constant := (68856732356973951658291631488181346228842991538736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38667129417985914929/10000000000000000000)
  centralHi := (386671294179859149291/100000000000000000000)
  directionLo := (194940119805056608837/50000000000000000000)
  directionHi := (15595209584404528707/4000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree062.table
  base := (3334035366171948795959124274990358284019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-5590490711114236390688603244500000000000000)
      constant := (97797866107716855496075366118574488989053007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree062.table
  base := (3333900364443149760571871300887614493147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-4059152347374970265110986073788828000000000000000)
      constant := (71026685802733247491503678461025996464284769134064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194940119805056608837/50000000000000000000)
  centralHi := (15595209584404528707/4000000000000000000)
  directionLo := (98265747063177937513/25000000000000000000)
  directionHi := (393062988252711750053/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree063.table
  base := (88715769615391498197061152334943444777/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-5674688166817538346187177460500000000000000)
      constant := (100831966650923451308720441375687600128659050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree063.table
  base := (2217832971846496494277661274615187566989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-457809736645740393578330462179138000000000000000)
      constant := (8136694085964263609365012725548940119750724867104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98265747063177937513/25000000000000000000)
  centralHi := (393062988252711750053/100000000000000000000)
  directionLo := (198110085703544845307/50000000000000000000)
  directionHi := (79244034281417938123/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree064.table
  base := (278563413055234812291164727183673527461/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-5758885622520840301685751676500000000000000)
      constant := (103912336382125312759719713138814693939108660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree064.table
  base := (5571157058178884009588173788251370118211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-4181422912248356819298962245435656000000000000000)
      constant := (75467411610911315148274531231715813596437361400432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198110085703544845307/50000000000000000000)
  centralHi := (79244034281417938123/20000000000000000000)
  directionLo := (1996761977086751159/500000000000000000)
  directionHi := (399352395417350231801/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree065.table
  base := (6740389776761983633765839590246937775241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-5843083078224142257184325892500000000000000)
      constant := (107038970800010427403057669648283087702087773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree065.table
  base := (3370144438851689308592688916400401662763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-4242558194685050096392950331259070000000000000000)
      constant := (77738177050767354269890919516681938207372269151712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1996761977086751159/500000000000000000)
  centralHi := (399352395417350231801/100000000000000000000)
  directionLo := (25153765189493110303/6250000000000000000)
  directionHi := (402460243031889764849/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree066.table
  base := (3971538629039166379736571483832326987893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-5927280533927444212682900108500000000000000)
      constant := (110211865888786650710081310765286226660716658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree066.table
  base := (7942985724204715091175555234397734984713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-478188164124638152609659824120276000000000000000)
      constant := (8893615575743453262212128586488757686785131621584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25153765189493110303/6250000000000000000)
  centralHi := (402460243031889764849/100000000000000000000)
  directionLo := (405544274669239898051/100000000000000000000)
  directionHi := (101386068667309974513/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree067.table
  base := (917926309858019226677523539707332081619/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-6011477989630746168181474324500000000000000)
      constant := (113431018065310884458913628118044886003258070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree067.table
  base := (4589590037451511954491848044820296503329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-4364828759558436650580926502905898000000000000000)
      constant := (82380498405884522502815734147453759333872968648096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405544274669239898051/100000000000000000000)
  centralHi := (101386068667309974513/25000000000000000000)
  directionLo := (408605029597913800841/100000000000000000000)
  directionHi := (204302514798956900421/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree068.table
  base := (163263858867507627116080773570156100059/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-6095675445334048123680048540500000000000000)
      constant := (116696424132053533726481745495949969491400128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree068.table
  base := (10448811675491845943584578751664345391411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-4425964041995129927674914588729312000000000000000)
      constant := (84752049405189053675585011949646425213781360958832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408605029597913800841/100000000000000000000)
  centralHi := (204302514798956900421/50000000000000000000)
  directionLo := (51455378379661411983/12500000000000000000)
  directionHi := (82328605407458259173/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree069.table
  base := (11751895020137588761510607882148010906291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-6179872901037350079178622756500000000000000)
      constant := (120008081235242232037777673015753844578033423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree069.table
  base := (11751826751001005209080257280561222595499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-498566591603535911640989186061414000000000000000)
      constant := (9684132345636108610543002863316665323892116069232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51455378379661411983/12500000000000000000)
  centralHi := (82328605407458259173/20000000000000000000)
  directionLo := (5183234589823837931/1250000000000000000)
  directionHi := (414658767185907034481/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree070.table
  base := (20941182711495282058872309547405618071/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-6264070356740652034677196972500000000000000)
      constant := (123365986827604391421315519753757811098601875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree070.table
  base := (13088177303382526674280713953744520479597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-4548234606868516481862890760376140000000000000000)
      constant := (89595921675867618045568604800944928756893733176464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5183234589823837931/1250000000000000000)
  centralHi := (414658767185907034481/100000000000000000000)
  directionLo := (41765273218290859401/10000000000000000000)
  directionHi := (417652732182908594011/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree071.table
  base := (903617286658333570707409247055132580657/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-6348267812443953990175771188500000000000000)
      constant := (126770138635194725832357173659502752428397136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree071.table
  base := (14457820486127575089599697092752379113343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5418720000000000000000000000000000000000000000
      center := (35220681)
      previous := (0)
      next := (31429575)
      square := (814718637801064950534346563792000000000000000)
      linear := (-64920702666270559985308152763374000000000000000)
      constant := (1296735766932211428195069283742196229674905398096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41765273218290859401/10000000000000000000)
  centralHi := (417652732182908594011/100000000000000000000)
  directionLo := (420625387007917642193/100000000000000000000)
  directionHi := (210312693503958821097/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree072.table
  base := (15860768890766640376680012772145109387419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-6432465268147255945674345404500000000000000)
      constant := (130220534627852618057227399828923690797533207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree072.table
  base := (15860718047330178636394714337913905084301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-518945019082433670672318548002552000000000000000)
      constant := (10508238107557882808630872915120967548209407217168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420625387007917642193/100000000000000000000)
  centralHi := (210312693503958821097/50000000000000000000)
  directionLo := (42357718032404981203/10000000000000000000)
  directionHi := (423577180324049812031/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree073.table
  base := (8648440952823810084867778207964023066957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-6516662723850557901172919620500000000000000)
      constant := (133717172992886015530709564592044186445097442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree073.table
  base := (4324208958397744640613627390595720075409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-4731640454178596313144855017846382000000000000000)
      constant := (97113630909388691642922162609745640251651375284032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42357718032404981203/10000000000000000000)
  centralHi := (423577180324049812031/100000000000000000000)
  directionLo := (213254272634210503187/50000000000000000000)
  directionHi := (3412068362147368051/800000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree074.table
  base := (18766185090221034676995864777449938303589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-6600860179553859856671493836500000000000000)
      constant := (137260052111624290435628734301204846730090217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree074.table
  base := (1172883959251080159188151225537077457189/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-4792775736615289590238843103669796000000000000000)
      constant := (99686702102985981672482829716648047889961858629888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213254272634210503187/50000000000000000000)
  centralHi := (3412068362147368051/800000000000000000)
  directionLo := (17176796007763350063/4000000000000000000)
  directionHi := (53677487524260468947/12500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree075.table
  base := (2533581396257737150771917214205032957267/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-6685057635257161812170068052500000000000000)
      constant := (140849170538522918477293772148822933973881208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree075.table
  base := (20268613356338155319550582744506374670959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-539323446561331429703647909943690000000000000000)
      constant := (11365928389003456254393306500602560213739426062512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17176796007763350063/4000000000000000000)
  centralHi := (53677487524260468947/12500000000000000000)
  directionLo := (432311649366991925413/100000000000000000000)
  directionHi := (216155824683495962707/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree076.table
  base := (21804255785861928687082616654104592012097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-6769255090960463767668642268500000000000000)
      constant := (144484526982538560864984536130667543376641141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree076.table
  base := (4360844307165454075809664206623242444773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-4915046301488676144426819275316624000000000000000)
      constant := (104933590167757955934535681686147846118662082444880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432311649366991925413/100000000000000000000)
  centralHi := (216155824683495962707/50000000000000000000)
  directionLo := (43518418362128131187/10000000000000000000)
  directionHi := (435184183621281311871/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree077.table
  base := (4674595436028072611215276480734705595517/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-6853452546663765723167216484500000000000000)
      constant := (148166120290524736997328036329394696982812005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree077.table
  base := (23372946162322370973160723008548750371837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-4976181583925369421520807361140038000000000000000)
      constant := (107607405267374747829716304632172099008265652179344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43518418362128131187/10000000000000000000)
  centralHi := (435184183621281311871/100000000000000000000)
  directionLo := (438037880975873146259/100000000000000000000)
  directionHi := (21901894048793657313/5000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree078.table
  base := (12487397958946676740757715294522245323319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-6937650002367067678665790700500000000000000)
      constant := (151893949432426242992247288913219358004271814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree078.table
  base := (12487383915578863947898289614696601249399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-559701874040229188734977271884828000000000000000)
      constant := (12257200005925276109546650042075870471459381728864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438037880975873146259/100000000000000000000)
  centralHi := (21901894048793657313/5000000000000000000)
  directionLo := (110218276803788685669/25000000000000000000)
  directionHi := (440873107215154742677/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree079.table
  base := (6652423659365865180275841973047619967403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-7021847458070369634164364916500000000000000)
      constant := (155668013488075234569900585036286095433089436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree079.table
  base := (26609669208293069630059228620667484584147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-5098452148798755975708783532786866000000000000000)
      constant := (113055773858725161432620647171048440703167244126064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110218276803788685669/25000000000000000000)
  centralHi := (440873107215154742677/100000000000000000000)
  directionLo := (443690216436262484809/100000000000000000000)
  directionHi := (44369021643626248481/10000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree080.table
  base := (14138828914162306726322284054599872466653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-7106044913773671589662939132500000000000000)
      constant := (159488311635413829950211556509787586481465218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree080.table
  base := (14138817404168115246094922288429971386863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-5159587431235449252802771618610280000000000000000)
      constant := (115830326087799647093978021844051809814658596310112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443690216436262484809/100000000000000000000)
  centralHi := (44369021643626248481/10000000000000000000)
  directionLo := (223244775782642653997/50000000000000000000)
  directionHi := (89297910313057061599/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree081.table
  base := (14989335816422387796947867209180655320879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-7190242369476973545161513348500000000000000)
      constant := (163354843139987531220821308602173149464013174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree081.table
  base := (29978650796523476333351663740431374731769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-580080301519126947766306633825966000000000000000)
      constant := (13182050689809699365032486966519279034399374704592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223244775782642653997/50000000000000000000)
  centralHi := (89297910313057061599/20000000000000000000)
  directionLo := (17970857793780760431/4000000000000000000)
  directionHi := (56158930605564876347/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree082.table
  base := (31712723669413837875997594537648658808441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-7274439825180275500660087564500000000000000)
      constant := (167267607345571002590480299882495378916847373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree082.table
  base := (6342540962409325107190956323928908530637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-5281857996108835806990747790257108000000000000000)
      constant := (121480163744631817586310175687314533710776233024720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17970857793780760431/4000000000000000000)
  centralHi := (56158930605564876347/12500000000000000000)
  directionLo := (226018109146365640961/50000000000000000000)
  directionHi := (452036218292731281923/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree083.table
  base := (33479802874612805891583555159768377910699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-7358637280883577456158661780500000000000000)
      constant := (171226603665803037355598100905467724029267047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree083.table
  base := (4184973226300565135740937171319186183327/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-5342993278545529084084735876080522000000000000000)
      constant := (124355448271919095899330837501715418479042044305792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226018109146365640961/50000000000000000000)
  centralHi := (452036218292731281923/100000000000000000000)
  directionLo := (90956836828048484379/20000000000000000000)
  directionHi := (56848023017530302737/12500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree084.table
  base := (7055979872471287763827477693000749220659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-7442834736586879411657235996500000000000000)
      constant := (175231831576721117752634351596645198543474635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree084.table
  base := (35279883922712381602775993682920950400269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-600458728998024706797635995767104000000000000000)
      constant := (14140478823384932610240376776883925625300657112592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90956836828048484379/20000000000000000000)
  centralHi := (56848023017530302737/12500000000000000000)
  directionLo := (2287578226202428943/500000000000000000)
  directionHi := (457515645240485788601/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree085.table
  base := (37113004298168847605551517740586566276851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-7527032192290181367155810212500000000000000)
      constant := (179283290610098021661774350390251088012673103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree085.table
  base := (37112990330129810757360415870058201114867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-5465263843418915638272712047727350000000000000000)
      constant := (130206746820981239854791715492980507293870579982704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2287578226202428943/500000000000000000)
  centralHi := (457515645240485788601/100000000000000000000)
  directionLo := (115057723864895899377/25000000000000000000)
  directionHi := (460230895459583597509/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree086.table
  base := (38979109786953488545794474339784083904349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-7611229647993483322654384428500000000000000)
      constant := (183380980347493632266651429448008556446930497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree086.table
  base := (19489548575885037626099577664092479220149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-5526399125855608915366700133550764000000000000000)
      constant := (133182760200268973215094331255359266775797242207776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115057723864895899377/25000000000000000000)
  centralHi := (460230895459583597509/100000000000000000000)
  directionLo := (462930220045356604313/100000000000000000000)
  directionHi := (231465110022678302157/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree087.table
  base := (5109776096599799661358152360834529025529/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-7695427103696785278152958644500000000000000)
      constant := (187524900414944615456768533682993840306824296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree087.table
  base := (4087819734463258058111754793737045713103/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-620837156476922465828965357708242000000000000000)
      constant := (15132483253040316831631944107752883921789098851040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462930220045356604313/100000000000000000000)
  centralHi := (231465110022678302157/50000000000000000000)
  directionLo := (116403473994269820189/25000000000000000000)
  directionHi := (465613895977079280757/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree088.table
  base := (10702573737379241500926527669024247343517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-7779624559400087233651532860500000000000000)
      constant := (191715050478223081016761608137833140436825604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree088.table
  base := (2140514230712992375292198783659395846587/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-5648669690728995469554676305197592000000000000000)
      constant := (139235513810096765977095361643879187487578143026880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116403473994269820189/25000000000000000000)
  centralHi := (465613895977079280757/100000000000000000000)
  directionLo := (468282192297194368583/100000000000000000000)
  directionHi := (58535274037149296073/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree089.table
  base := (44775362680766338433884714839070755492619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-7863822015103389189150107076500000000000000)
      constant := (195951430238602857565357733764470750041108807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree089.table
  base := (44775353334961986061074315023424706143141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-5709804973165688746648664391021006000000000000000)
      constant := (142312253582034044616393096680546475845570923096592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468282192297194368583/100000000000000000000)
  centralHi := (58535274037149296073/12500000000000000000)
  directionLo := (94187074085222255497/20000000000000000000)
  directionHi := (235467685213055638743/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree090.table
  base := (46773406928711585467379928082810086974681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-7948019470806691144648681292500000000000000)
      constant := (200234039429078693859513792088388934609658093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree090.table
  base := (5846674809822209874974035816331135294703/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-641215583955820224860294719649380000000000000000)
      constant := (16158063155525186613592462499738293466491735631232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94187074085222255497/20000000000000000000)
  centralHi := (235467685213055638743/50000000000000000000)
  directionLo := (473573684461130888997/100000000000000000000)
  directionHi := (236786842230565444499/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree091.table
  base := (6100552898789499512746580633623036366803/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-8032216926509993100147255508500000000000000)
      constant := (204562877810989644216112170526656167419524472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree091.table
  base := (12201103887713197872883494025601464778689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-5832075538039075300836640562667834000000000000000)
      constant := (148566458090267626859943986009119095293506405489472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473573684461130888997/100000000000000000000)
  centralHi := (236786842230565444499/50000000000000000000)
  directionLo := (476197381460464231761/100000000000000000000)
  directionHi := (238098690730232115881/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree092.table
  base := (25434203720218820038710912698150164887921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-8116414382213295055645829724500000000000000)
      constant := (208937945171003186331360093938003917478119626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree092.table
  base := (6358550066827185320774504247759814444111/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-5893210820475768577930628648491248000000000000000)
      constant := (151743922499104664848531786408878309305956891369856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476197381460464231761/100000000000000000000)
  centralHi := (238098690730232115881/50000000000000000000)
  directionLo := (14962709428538861569/3125000000000000000)
  directionHi := (478806701713243570209/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree093.table
  base := (13241339020250303163320871484803155358931/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-8200611837916597011144403940500000000000000)
      constant := (213359241318421329054014031216778268936093372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree093.table
  base := (26482674919515745031682993115870242765199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-661594011434717983891624081590518000000000000000)
      constant := (17217217943120856897326787189267348999349808397664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14962709428538861569/3125000000000000000)
  centralHi := (478806701713243570209/100000000000000000000)
  directionLo := (481401878996361129523/100000000000000000000)
  directionHi := (120350469749090282381/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree094.table
  base := (55095265895593284598852982012620960423883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-8284809293619898966642978156500000000000000)
      constant := (217826766082774160634846636194668910902465799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree094.table
  base := (13773815063561579935170667680256241405657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-6015481385349155132118604820138076000000000000000)
      constant := (158199574933724549889853013229843255802202392252736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481401878996361129523/100000000000000000000)
  centralHi := (120350469749090282381/25000000000000000000)
  directionLo := (3781118287647753547/781250000000000000)
  directionHi := (483983140818912454017/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree095.table
  base := (14314533502224884161887107491155727974913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-8369006749323200922141552372500000000000000)
      constant := (222340519311670022152729069038125014330681556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree095.table
  base := (28629064455451737873928635589100464531017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-6076616667785848409212592905961490000000000000000)
      constant := (161477762725622601382967045185183177849621876623008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3781118287647753547/781250000000000000)
  centralHi := (483983140818912454017/100000000000000000000)
  directionLo := (243275354327483902049/50000000000000000000)
  directionHi := (486550708654967804099/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree096.table
  base := (29726978925232659615616010290606266842721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-8453204205026502877640126588500000000000000)
      constant := (226900500868874817180550025858804264285328426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree096.table
  base := (59453953243950585380647138837855487167853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-681972438913615742922953443531656000000000000000)
      constant := (18309947196121870260537961235203029825169548633104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243275354327483902049/50000000000000000000)
  centralHi := (486550708654967804099/100000000000000000000)
  directionLo := (97820959633069125117/20000000000000000000)
  directionHi := (244552399082672812793/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree097.table
  base := (61682735122316797919333725153755217668553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-8537401660729804833138700804500000000000000)
      constant := (231506710632595932493489295135149026536433309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree097.table
  base := (1542068274007828707735151997190766544089/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-6198887232659234963400569077608318000000000000000)
      constant := (168134860963925989314850382019097734526031208686720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97820959633069125117/20000000000000000000)
  centralHi := (244552399082672812793/50000000000000000000)
  directionLo := (245822809704508300553/50000000000000000000)
  directionHi := (491645619409016601107/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree098.table
  base := (63944463770029778935753620269939265939633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-8621599116433106788637275020500000000000000)
      constant := (236159148493948885821413580926306781094800549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree098.table
  base := (15986115002502358845411094712249276409141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-6260022515095928240494557163431732000000000000000)
      constant := (171513771243241305625701666487484078683410230754368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245822809704508300553/50000000000000000000)
  centralHi := (491645619409016601107/100000000000000000000)
  directionLo := (247086688522362390351/50000000000000000000)
  directionHi := (494173377044724780703/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree099.table
  base := (66239141956877728507080900041073707505063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-8705796572136408744135849236500000000000000)
      constant := (240857814355587170874332110520176906497768339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree099.table
  base := (6623913856034044549250751305206597065981/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-702350866392513501954282805472794000000000000000)
      constant := (19436250614725945987266725966500629132765494674080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247086688522362390351/50000000000000000000)
  centralHi := (494173377044724780703/100000000000000000000)
  directionLo := (496688270523373483491/100000000000000000000)
  directionHi := (124172067630843370873/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree100.table
  base := (68566768040730100343887051742826049068559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-8789994027839710699634423452500000000000000)
      constant := (245602708130477868698905172742369780600633627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree100.table
  base := (68566764972826396420203962592709682483837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-6382293079969314794682533335078560000000000000000)
      constant := (178372313768765525618748834024544736455748602323344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496688270523373483491/100000000000000000000)
  centralHi := (124172067630843370873/25000000000000000000)
  directionLo := (499190494271687789751/100000000000000000000)
  directionHi := (62398811783960973719/12500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree101.table
  base := (1418546811068147926344070886440827849737/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-8874191483543012655132997668500000000000000)
      constant := (250393829740807465894297435447068193801803050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree101.table
  base := (8865917222824563221953184577240019140633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-6443428362406008071776521420901974000000000000000)
      constant := (181851945895579496123519255972059596361707112266368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499190494271687789751/100000000000000000000)
  centralHi := (62398811783960973719/12500000000000000000)
  directionLo := (62710029733454031781/12500000000000000000)
  directionHi := (501680237867632254249/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree102.table
  base := (36660429091115438179329927966474331291079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-8958388939246314610631571884500000000000000)
      constant := (255231179117003989236885260976446279116854374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree102.table
  base := (73320855679970281118541515290198931172383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-722729293871411260985612167413932000000000000000)
      constant := (20596127984732022562882460524685518854609905332144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62710029733454031781/12500000000000000000)
  centralHi := (501680237867632254249/100000000000000000000)
  directionLo := (126039421552007935467/25000000000000000000)
  directionHi := (504157686208031741869/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree103.table
  base := (3029892790141316898688744306435703761151/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-9042586394949616566130146100500000000000000)
      constant := (260114756196863054972613668248027307483525075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree103.table
  base := (37873658746998300674265770830569658584247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-6565698927279394625964497592548802000000000000000)
      constant := (188911931624741747007619677793866156956663558834528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126039421552007935467/25000000000000000000)
  centralHi := (504157686208031741869/100000000000000000000)
  directionLo := (101324603933762962197/20000000000000000000)
  directionHi := (253311509834407405493/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree104.table
  base := (19551681054479779941474740843200244700101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-9126783850652918521628720316500000000000000)
      constant := (265044560924766759113002672946758451876421412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree104.table
  base := (78206722177741905836085409085927257292937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-6626834209716087903058485678372216000000000000000)
      constant := (192492285141761545200606046712176031808232523422544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101324603933762962197/20000000000000000000)
  centralHi := (253311509834407405493/50000000000000000000)
  directionLo := (15908637945571020723/3125000000000000000)
  directionHi := (509076414258272663137/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree105.table
  base := (40349535318547737512303627109938890323731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-9210981306356220477127294532500000000000000)
      constant := (270020593250985520016857310623653522374315486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree105.table
  base := (80699068795141143466161375777870539020903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-743107721350309020016941529355070000000000000000)
      constant := (21789579153070494367452972074334795775849307475504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15908637945571020723/3125000000000000000)
  centralHi := (509076414258272663137/100000000000000000000)
  directionLo := (818428866821923473/160000000000000000)
  directionHi := (255759020881851085313/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree106.table
  base := (41612179086047071843187829467085853312459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-9295178762059522432625868748500000000000000)
      constant := (275042853131054041922658286751511100451120654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree106.table
  base := (83224356509245064411380190230419675916231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-6749104774589474457246461850019044000000000000000)
      constant := (199753713300160584489957006530540201664593674634672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (818428866821923473/160000000000000000)
  centralHi := (255759020881851085313/50000000000000000000)
  directionLo := (32121754368236170827/6250000000000000000)
  directionHi := (513948069891778733233/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree107.table
  base := (8578258607274884157394680202125334104687/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-9379376217762824388124442964500000000000000)
      constant := (280111340525213511769010960429126427075484110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree107.table
  base := (85782584571715224267158588445136116550061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-6810240057026167734340449935842458000000000000000)
      constant := (203434787880549191631452395984272456327552240447632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32121754368236170827/6250000000000000000)
  centralHi := (513948069891778733233/100000000000000000000)
  directionLo := (32272916400186472599/6250000000000000000)
  directionHi := (103273332480596712317/20000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree108.table
  base := (44186876834143504873077863660565662319827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-9463573673466126343623017180500000000000000)
      constant := (285226055397912983932033588980019960205901662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree108.table
  base := (88373752313433945672530970239955573375171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-763486148829206779048270891296208000000000000000)
      constant := (23016604010339707245867788362153131406485832985328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32272916400186472599/6250000000000000000)
  centralHi := (103273332480596712317/20000000000000000000)
  directionLo := (103754795848078062099/20000000000000000000)
  directionHi := (16211686851262197203/3125000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree109.table
  base := (22749465089729996882843937440792024657567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-9547771129169428299121591396500000000000000)
      constant := (290386997717363659396129958095447909227404204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree109.table
  base := (18199571827222130740244912255260471039543/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-6932510621899554288528426107489286000000000000000)
      constant := (210897657914667124594462205420733499884414431796080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103754795848078062099/20000000000000000000)
  centralHi := (16211686851262197203/3125000000000000000)
  directionLo := (521170176653097674577/100000000000000000000)
  directionHi := (260585088326548837289/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree110.table
  base := (93654905608325114024762761044754648270747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-9631968584872730254620165612500000000000000)
      constant := (295594167455140437133343330035371996358349591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree110.table
  base := (46827452252389326231593869082479901078861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-6993645904336247565622414193312700000000000000000)
      constant := (214679453324796743162500008686227933701951448626464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521170176653097674577/100000000000000000000)
  centralHi := (260585088326548837289/50000000000000000000)
  directionLo := (130888851828644376157/25000000000000000000)
  directionHi := (523555407314577504629/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree111.table
  base := (96344888936924986578997537892079373182557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-9716166040576032210118739828500000000000000)
      constant := (300847564585825714803365785966280206778675521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree111.table
  base := (96344887941087705686145882470447548718979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-783864576308104538079600253237346000000000000000)
      constant := (24277202478338077152404563957884407814442332421872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130888851828644376157/25000000000000000000)
  centralHi := (523555407314577504629/100000000000000000000)
  directionLo := (131482455109048027417/25000000000000000000)
  directionHi := (525929820436192109669/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree112.table
  base := (3962712396635168096290110369994350645577/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-9800363496279334165617314044500000000000000)
      constant := (306147189086690951058495477872242514605389525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree112.table
  base := (49533904508653934908513265990700592462147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-7115916469209634119810390364959528000000000000000)
      constant := (222343764838948961743803082056647561424288089724128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131482455109048027417/25000000000000000000)
  centralHi := (525929820436192109669/100000000000000000000)
  directionLo := (105658712375223917497/20000000000000000000)
  directionHi := (264146780938059793743/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree113.table
  base := (25455917040428231694447421457667124418087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-9884560951982636121115888260500000000000000)
      constant := (311493040937411979657950252571025430376634444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree113.table
  base := (50911833675484517365739585667995915696091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-7177051751646327396904378450782942000000000000000)
      constant := (226226280911800806389541581558621316349370255573984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105658712375223917497/20000000000000000000)
  centralHi := (264146780938059793743/50000000000000000000)
  directionLo := (132661693560978048737/25000000000000000000)
  directionHi := (530646774243912194949/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree114.table
  base := (104612463331514684659285728068250374706083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-9968758407685938076614462476500000000000000)
      constant := (316885120119814492425070012815617269859422399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree114.table
  base := (13076557825008583828977338573315437083563/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-804243003787002297110929615178484000000000000000)
      constant := (25571374501160043897352539753407257624806627507072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132661693560978048737/25000000000000000000)
  centralHi := (530646774243912194949/100000000000000000000)
  directionLo := (33311849812556240863/6250000000000000000)
  directionHi := (532989597000899853809/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree115.table
  base := (107434195118642965704914648987611606423137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-10052955863389240032113036692500000000000000)
      constant := (322323426617646489311472968046343415140426261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree115.table
  base := (107434194458787463704163902346642064443819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-7299322316519713951092354622429770000000000000000)
      constant := (234092033623101968255435073344471608328345377330928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33311849812556240863/6250000000000000000)
  centralHi := (532989597000899853809/100000000000000000000)
  directionLo := (107064433311327764023/20000000000000000000)
  directionHi := (133830541639159705029/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree116.table
  base := (55144431624443828770263893585127119556833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-10137153319092541987611610908500000000000000)
      constant := (327807960416374834361329239208023474673024298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree116.table
  base := (55144431326829469961841623982185360766717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-7360457598956407228186342708253184000000000000000)
      constant := (238075270239264474337220599956737090904932311339808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107064433311327764023/20000000000000000000)
  centralHi := (133830541639159705029/25000000000000000000)
  directionLo := (26882230818079713157/5000000000000000000)
  directionHi := (537644616361594263141/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree117.table
  base := (113176467477038061847451238900505648039633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-10221350774795843943110185124500000000000000)
      constant := (333338721503003360563749109403726799346100549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree117.table
  base := (28294116735036227094422668636034357837827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-824621431265900056142258977119622000000000000000)
      constant := (26899120038835535224656274080918962466642768196544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26882230818079713157/5000000000000000000)
  centralHi := (537644616361594263141/100000000000000000000)
  directionLo := (33747317312264684087/6250000000000000000)
  directionHi := (539957076996234945393/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree118.table
  base := (58048503791907187598608171042621762007657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-10305548230499145898608759340500000000000000)
      constant := (338915709865910238337023739542517906772811642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree118.table
  base := (116097007099573676054210954265440936967999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-7482728163829793782374318879900012000000000000000)
      constant := (246142463945455059507351935772954225559167372343088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33747317312264684087/6250000000000000000)
  centralHi := (539957076996234945393/100000000000000000000)
  directionLo := (67782459532088539529/12500000000000000000)
  directionHi := (542259676256708316233/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree119.table
  base := (59525241686562048782347290476473819226983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-10389745686202447854107333556500000000000000)
      constant := (344538925494702565179821318288506224838060198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree119.table
  base := (5952524146820128036224798500564672478233/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-7543863446266487059468306965723426000000000000000)
      constant := (250226421019547105387926416910780216078777602489920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67782459532088539529/12500000000000000000)
  centralHi := (542259676256708316233/100000000000000000000)
  directionLo := (544552539237255079057/100000000000000000000)
  directionHi := (272276269618627539529/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree120.table
  base := (61018447334804462205019548082925396617933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-10473943141905749809605907772500000000000000)
      constant := (350208368380086350951529962096790092041500898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree120.table
  base := (61018447137885157886895476501074078569297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-844999858744797815173588339060760000000000000000)
      constant := (28260439062785392590045572446768086873395033196192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544552539237255079057/100000000000000000000)
  centralHi := (272276269618627539529/50000000000000000000)
  directionLo := (136708947102378405387/25000000000000000000)
  directionHi := (546835788409513621549/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree121.table
  base := (6252812065822566768594199917685775134457/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-10558140597609051765104481988500000000000000)
      constant := (355924038513750267072997278830746921642524420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree121.table
  base := (31264060240327183188081838977131252881317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-7666134011139873613656283137370254000000000000000)
      constant := (258495055576003402951517539361577002005710621540416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136708947102378405387/25000000000000000000)
  centralHi := (546835788409513621549/100000000000000000000)
  directionLo := (274554771849428284363/50000000000000000000)
  directionHi := (549109543698856568727/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree122.table
  base := (64054261586706680266529978935590380409879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-10642338053312353720603056204500000000000000)
      constant := (361685935888261701138613294019172580323447174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree122.table
  base := (128108522853185950563980864778755949176987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-7727269293576566890750271223193668000000000000000)
      constant := (262679733046971975424501164661049978852162693276144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274554771849428284363/50000000000000000000)
  centralHi := (549109543698856568727/100000000000000000000)
  directionLo := (275686961278947045907/50000000000000000000)
  directionHi := (110274784511578818363/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree123.table
  base := (16399217514385365684834980254151003321123/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-10726535509015655676101630420500000000000000)
      constant := (367494060496973813204388989629760025408156152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree123.table
  base := (65596869913178458058520304681087558970721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-865378286223695574204917701001898000000000000000)
      constant := (29655331552573711489525367519859380792072302135456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275686961278947045907/50000000000000000000)
  centralHi := (110274784511578818363/20000000000000000000)
  directionLo := (110725808007454289399/20000000000000000000)
  directionHi := (138407260009317861749/25000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree124.table
  base := (134311892029305786074473347033994123008323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-10810732964718957631600204636500000000000000)
      constant := (373348412333942428331208039560801688519441119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree124.table
  base := (16788986471124880875456528015804525583289/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-7849539858449953444938247394840496000000000000000)
      constant := (271149808350275546522608839300688553975741010940544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110725808007454289399/20000000000000000000)
  centralHi := (138407260009317861749/25000000000000000000)
  directionLo := (111175001770776298997/20000000000000000000)
  directionHi := (277937504426940747493/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree125.table
  base := (137462978815783396179777669638707460296341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-10894930420422259587098778852500000000000000)
      constant := (379248991393851723573615315240851495395706073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree125.table
  base := (137462978581113475447666525461113501192321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-7910675140886646722032235480663910000000000000000)
      constant := (275435206174461157135091336286996608840884060908752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111175001770776298997/20000000000000000000)
  centralHi := (277937504426940747493/50000000000000000000)
  directionLo := (558111939456606634993/100000000000000000000)
  directionHi := (279055969728303317497/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree126.table
  base := (140647000384819135953152928114585462116061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-10979127876125561542597353068500000000000000)
      constant := (385195797671947778080014502938073029492151233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree126.table
  base := (28129400034654866782594477402890602424573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-885756713702593333236247062943036000000000000000)
      constant := (31083797493586640190103926494589631023726435370320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558111939456606634993/100000000000000000000)
  centralHi := (279055969728303317497/50000000000000000000)
  directionLo := (140084985022424661901/25000000000000000000)
  directionHi := (112067988017939729521/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree127.table
  base := (17982994582024648927533564451906249704847/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-11063325331828863498095927284500000000000000)
      constant := (391188831163979153709766080489608249874855128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree127.table
  base := (143863956465510402779108097689748417772869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-8032945705760033276220211652310738000000000000000)
      constant := (284106722150654634555150148983225759366614825024528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140084985022424661901/25000000000000000000)
  centralHi := (112067988017939729521/20000000000000000000)
  directionLo := (562559116853899354919/100000000000000000000)
  directionHi := (14063977921347483873/2500000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree128.table
  base := (147113847558180041138490953611550405801901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-11147522787532165453594501500500000000000000)
      constant := (397228091866143761826410473533412171507500753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree128.table
  base := (147113847386305102927449232533338404550123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2500668351)
      previous := (0)
      next := (2231499825)
      square := (57845023283875611487938606029232000000000000000)
      linear := (-8094080988196726553314199738134152000000000000000)
      constant := (288492840296834324612763892820461033504477281768176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell133.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562559116853899354919/100000000000000000000)
  centralHi := (14063977921347483873/2500000000000000000)
  directionLo := (564769573765399749373/100000000000000000000)
  directionHi := (282384786882699874687/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree129.table
  base := (150396673026611994173625163695084722679717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3444)
      previous := (0)
      next := (3075)
      square := (79686877719196493596864883000000000000000)
      linear := (-11231720243235467409093075716500000000000000)
      constant := (403313579775041350810435342913839490302025001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree129.table
  base := (150396672871702301979258439908634939778011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6427224809319512387548734003248000000000000000)
      linear := (-906135141181491092267576424884174000000000000000)
      constant := (32545836875373139247878784129153888251744968526448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell133.Kernel129
