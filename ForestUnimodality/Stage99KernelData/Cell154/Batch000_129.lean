import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell154.Parameters
import ForestUnimodality.BinomialMassData.Q48539_91164.Batch000_049
import ForestUnimodality.BinomialMassData.Q48539_91164.Batch050_099
import ForestUnimodality.BinomialMassData.Q48539_91164.Batch100_149
import ForestUnimodality.BinomialMassData.Q97103_182328.Batch000_049
import ForestUnimodality.BinomialMassData.Q97103_182328.Batch050_099
import ForestUnimodality.BinomialMassData.Q97103_182328.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree000.table
  base := (1244248103723888813659570477/25000000000000000000000000)
  polynomial :=
    { denominator := 75970000000000000000000000000000000000000000
      center := (436851)
      previous := (0)
      next := (383625)
      square := (10001335677336084540312022586500000000000000)
      linear := (-45228286426511377988912698467700000000000000)
      constant := (3781021137596153326948702765507600000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree000.table
  base := (1244248103723888813659570477/25000000000000000000000000)
  polynomial :=
    { denominator := 151940000000000000000000000000000000000000000
      center := (873927)
      previous := (0)
      next := (767025)
      square := (20002671354672169080624045173000000000000000)
      linear := (-90456572853022755977825396935400000000000000)
      constant := (7562042275192306653897405531015200000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree001.table
  base := (296253221417466390081479427550366742757759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-3820575876503186758489235828821237350000000000000)
      constant := (155723073382070056155723985847409660379921817644879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree001.table
  base := (148100768533299826256153442621400765306307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-7641526803094273620148733358489468450000000000000)
      constant := (311393501738643499479188963101756491150468649192268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (6236723259902918233/12500000000000000000)
  directionHi := (9978757215844669173/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree002.table
  base := (2890418877808675517242503660178459165263/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-4548758125166511069742543725310422600000000000000)
      constant := (100156063413626283034654656195315756201181527750592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree002.table
  base := (92464939370376352367668027953491162777201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-9098266350508822345825610852314832700000000000000)
      constant := (200255480070911148579168049857010292283222358011524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6236723259902918233/12500000000000000000)
  centralHi := (9978757215844669173/20000000000000000000)
  directionLo := (705604689513795867/1000000000000000000)
  directionHi := (70560468951379586701/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree003.table
  base := (7620782435955432129187354069024339696313/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-586326708203315042332872402422178650000000000000)
      constant := (7779952459084873290188202697277966161257108384272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree003.table
  base := (121884352326016469614524770077110366115429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-1172778433102596785722498705126688550000000000000)
      constant := (15554827491467297528540950112280559831876221032922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (705604689513795867/1000000000000000000)
  centralHi := (70560468951379586701/100000000000000000000)
  directionLo := (43209286235593802063/50000000000000000000)
  directionHi := (86418572471187604127/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree004.table
  base := (84884180155125769795306194665892647455703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-6005122622493159692249159518288793100000000000000)
      constant := (53779053841785528373493835344076134848161270920743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree004.table
  base := (21211679201511836551258715974341354570609/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-12011745445337919797179365839965561200000000000000)
      constant := (107525776108526142161953294465791861467754598765832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43209286235593802063/50000000000000000000)
  centralHi := (86418572471187604127/100000000000000000000)
  directionLo := (6236723259902918233/6250000000000000000)
  directionHi := (99787572158446691729/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree005.table
  base := (3102628709281777441195811723153181689047/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-6733304871156484003502467414777978350000000000000)
      constant := (45310839040955004451798302445516288983784488080140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree005.table
  base := (7753001629545703678851853004666636619059/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-13468484992752468522856243333790925450000000000000)
      constant := (90601240113946289557167243605241973766716758242864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6236723259902918233/6250000000000000000)
  centralHi := (99787572158446691729/100000000000000000000)
  directionLo := (22313179465595221783/20000000000000000000)
  directionHi := (27891474331994027229/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree006.table
  base := (47147988396216700127747452455303554426511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-829054124424423146083975034585240400000000000000)
      constant := (4594207142577900553211836189844424834325416296999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree006.table
  base := (4712591889485005207121907154848231328597/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-1658358282240779694281457869735143300000000000000)
      constant := (9187231045878303799004335450475972229005213083460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22313179465595221783/20000000000000000000)
  centralHi := (27891474331994027229/25000000000000000000)
  directionLo := (24442863445935141103/20000000000000000000)
  directionHi := (30553579307418926379/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree007.table
  base := (36790220941036601074128069925370846211063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-8189669368483132626009083207756348850000000000000)
      constant := (40134352402027379601336422936527364060362512760903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree007.table
  base := (9193154694036567820860884104042260616897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-16381964087581565974209998321441653950000000000000)
      constant := (80266140921945419673963918346500755607654375358856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24442863445935141103/20000000000000000000)
  centralHi := (30553579307418926379/25000000000000000000)
  directionLo := (132006549933081386287/100000000000000000000)
  directionHi := (8250409370817586643/6250000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree008.table
  base := (29142983350167172614444681885213913988539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-8917851617146456937262391104245534100000000000000)
      constant := (40716480663275108125923949684031461759828250426059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree008.table
  base := (2912839378585074955099756819539702078101/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-17838703634996114699886875815267018200000000000000)
      constant := (81437370881616941651017399881639159945260790315620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132006549933081386287/100000000000000000000)
  centralHi := (8250409370817586643/6250000000000000000)
  directionLo := (141120937902759173401/100000000000000000000)
  directionHi := (70560468951379586701/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree009.table
  base := (23192831164123546157779660604677738270069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-1071781540645531249835077666748302150000000000000)
      constant := (4729759548293649759573538120217882305963714724221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree009.table
  base := (23180287983060679648949104584875567840687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-2143938131378962602840417034343598050000000000000)
      constant := (9460716725490988900499727880448430563554312717966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141120937902759173401/100000000000000000000)
  centralHi := (70560468951379586701/50000000000000000000)
  directionLo := (149681358237670037593/100000000000000000000)
  directionHi := (74840679118835018797/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree010.table
  base := (1147979028964701229149517895468555061999/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-10374216114473105559769006897223904600000000000000)
      constant := (45391252537459910169676591106608446797161212677104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree010.table
  base := (18356555028267360925775931480014157711713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-20752182729825212151240630802917746700000000000000)
      constant := (90799415827863450882115019800168585943857547107106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149681358237670037593/100000000000000000000)
  centralHi := (74840679118835018797/50000000000000000000)
  directionLo := (39444501274887014787/25000000000000000000)
  directionHi := (157778005099548059149/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree011.table
  base := (2866864309824696056450710827253395491603/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-11102398363136429871022314793713089850000000000000)
      constant := (49013676396704364280831589444979199388100922343215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree011.table
  base := (14324268028637407090947510213668596298359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-22208922277239760876917508296743110950000000000000)
      constant := (98050402557469059929789704468771544720573792386958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39444501274887014787/25000000000000000000)
  centralHi := (157778005099548059149/100000000000000000000)
  directionLo := (33095793559008259377/20000000000000000000)
  directionHi := (82739483897520648443/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree012.table
  base := (1089076138691848398090724787933002807163/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-1314508956866639353586180298911363900000000000000)
      constant := (5925573489155168335564865504772270686107535116670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree012.table
  base := (10881533696791401229019927113148631946529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-2629517980517145511399376198952052800000000000000)
      constant := (11854407998501851504312392536116742193904881672722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33095793559008259377/20000000000000000000)
  centralHi := (82739483897520648443/50000000000000000000)
  directionLo := (43209286235593802063/25000000000000000000)
  directionHi := (172837144942375208253/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree013.table
  base := (494268693187071564153486419465120972563/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-12558762860463078493528930586691460350000000000000)
      constant := (58273864805341677822476258655686581344726941478448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree013.table
  base := (31599026346078695831916501903325219981/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-25122401372068858328271263284393839450000000000000)
      constant := (116583631531800779256750447647887279417617828030500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43209286235593802063/25000000000000000000)
  centralHi := (172837144942375208253/100000000000000000000)
  directionLo := (7195784161426846729/4000000000000000000)
  directionHi := (89947302017835584113/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree014.table
  base := (2650199141555910890906868586572559230117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-13286945109126402804782238483180645600000000000000)
      constant := (63799837042198018009627398544751028923506557805354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree014.table
  base := (2646226411084535267175233897504658170263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-26579140919483407053948140778219203700000000000000)
      constant := (127642436609437083413513113353882128270075015104412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7195784161426846729/4000000000000000000)
  centralHi := (89947302017835584113/50000000000000000000)
  directionLo := (186685453237444879127/100000000000000000000)
  directionHi := (23335681654680609891/12500000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree015.table
  base := (751401758194446878519698532002127053801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-1557236373087747457337282931074425650000000000000)
      constant := (7764017572923420738124620712867395054862143674436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree015.table
  base := (749550122115446320109528508341477366461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-3115097829655328419958335363560507550000000000000)
      constant := (15533586498634139638889827992423809381762384292392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186685453237444879127/100000000000000000000)
  centralHi := (23335681654680609891/12500000000000000000)
  directionLo := (38647560512813493769/20000000000000000000)
  directionHi := (96618901282033734423/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree016.table
  base := (978067027399682269268338804670289224337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-14743309606453051427288854276159016100000000000000)
      constant := (76479007978999455338705457998618805241975105346497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree016.table
  base := (971158030645273466117142022064329042533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-29492620014312504505301895765869932200000000000000)
      constant := (153015534238287982580022424557066339992083903243946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38647560512813493769/20000000000000000000)
  centralHi := (96618901282033734423/50000000000000000000)
  directionLo := (199575144316893383457/100000000000000000000)
  directionHi := (99787572158446691729/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree017.table
  base := (-817890694000264767200895504787660039111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-15471491855116375738542162172648201350000000000000)
      constant := (83589858993241739154068916919155948129398125746409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree017.table
  base := (-824334344348724291555396674958717794541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-30949359561727053230978773259695296450000000000000)
      constant := (167245158351303316938540406134950684721250089657158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199575144316893383457/100000000000000000000)
  centralHi := (99787572158446691729/50000000000000000000)
  directionLo := (205717350066609896307/100000000000000000000)
  directionHi := (51429337516652474077/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree018.table
  base := (-75341263034647136344594922111375940837/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-1799963789308855561088385563237487400000000000000)
      constant := (10132647479173792904141043897637869547728754549344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree018.table
  base := (-2416925969844025505714030302736930301909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-3600677678793511328517294528168962300000000000000)
      constant := (20273487577623861491607003781406736682802260986438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205717350066609896307/100000000000000000000)
  centralHi := (51429337516652474077/25000000000000000000)
  directionLo := (211681406854138760101/100000000000000000000)
  directionHi := (105840703427069380051/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree019.table
  base := (-1912300473772447678064147637941002304637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-16927856352443024361048777965626571850000000000000)
      constant := (99278665405485479895826778954326925408414276538406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree019.table
  base := (-3830192958808738345133337203993148958919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-33862838656556150682332528247346024950000000000000)
      constant := (198639731514545803259230161471256108860791443450322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211681406854138760101/100000000000000000000)
  centralHi := (105840703427069380051/50000000000000000000)
  directionLo := (217481971429971007103/100000000000000000000)
  directionHi := (1699077901796648493/781250000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree020.table
  base := (-2539337709777854900495025753778657121327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-17656038601106348672302085862115757100000000000000)
      constant := (107834118102081971270075739592024902173721476186626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree020.table
  base := (-5083876908392856297881959033920095361159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-35319578203970699408009405741171389200000000000000)
      constant := (215759679556076363189522644768616986124127201679442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217481971429971007103/100000000000000000000)
  centralHi := (1699077901796648493/781250000000000000)
  directionLo := (223131794655952217831/100000000000000000000)
  directionHi := (27891474331994027229/12500000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree021.table
  base := (-3094941917472169223623116478669943975909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-2042691205529963664839488195400549150000000000000)
      constant := (12983498905395226837985611061204181710984603654438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree021.table
  base := (-6194716833456390684607913391276047467659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-4086257527931694237076253692777417050000000000000)
      constant := (25978204760100939259495478548392496144721228402938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223131794655952217831/100000000000000000000)
  centralHi := (27891474331994027229/12500000000000000000)
  directionLo := (22864205141597493997/10000000000000000000)
  directionHi := (228642051415974939971/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree022.table
  base := (-7172549835746345961563356566159985871093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-19112403098432997294808701655094127600000000000000)
      constant := (126323341420097399165749598602756624219013655888667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree022.table
  base := (-7177035619302504844142823643304419745873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-38233057298799796859363160728822117700000000000000)
      constant := (252757341905554030254279737895283761143522173086974) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22864205141597493997/10000000000000000000)
  centralHi := (228642051415974939971/100000000000000000000)
  directionLo := (23402260054324802197/10000000000000000000)
  directionHi := (234022600543248021971/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree023.table
  base := (-8039012795092092653219204238645554111001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-19840585347096321606062009551583312850000000000000)
      constant := (136243262480054201114849817152673402162304511979319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree023.table
  base := (-201079298804459573919943139282761396759/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-39689796846214345585040038222647481950000000000000)
      constant := (272607358590290426014129522054544936676213655689680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23402260054324802197/10000000000000000000)
  centralHi := (234022600543248021971/100000000000000000000)
  directionLo := (47856438419232131873/20000000000000000000)
  directionHi := (119641096048080329683/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree024.table
  base := (-4399978982448176151282451247214876507811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-2285418621751071768590590827563610900000000000000)
      constant := (16289522565714883533917356164944919612687408502602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree024.table
  base := (-8803810393440424686925102020724409772393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-4571837377069877145635212857385871800000000000000)
      constant := (32593643682058186822786936104599597076225026978526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47856438419232131873/20000000000000000000)
  centralHi := (119641096048080329683/50000000000000000000)
  directionLo := (24442863445935141103/10000000000000000000)
  directionHi := (244428634459351411031/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree025.table
  base := (-2366169061648895952807594194818864249099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-21296949844422970228568625344561683350000000000000)
      constant := (157405837284267308947925521043902854617482807570324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree025.table
  base := (-18492658442198161174662200511192824373/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-42603275941043443036393793210298210450000000000000)
      constant := (314953994360495850389371912169166021605423231026688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24442863445935141103/10000000000000000000)
  centralHi := (244428634459351411031/100000000000000000000)
  directionLo := (124734465198058364661/50000000000000000000)
  directionHi := (249468930396116729323/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree026.table
  base := (-5020636618843999884422330374873942855539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-22025132093086294539821933241050868600000000000000)
      constant := (168639454770631461579356570970301200869670296293882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree026.table
  base := (-627785561112852669216471180907736078963/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-44060015488457991762070670704123574700000000000000)
      constant := (337432542468612530161470329226234811970805859174304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124734465198058364661/50000000000000000000)
  centralHi := (249468930396116729323/100000000000000000000)
  directionLo := (63602347206245970987/25000000000000000000)
  directionHi := (254409388824983883949/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree027.table
  base := (-10536840333867085054296629549636748498377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-2528146037972179872341693459726672650000000000000)
      constant := (20033652452124833119458864801479088601984533985807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree027.table
  base := (-10539884565293801763251617587029418788217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-5057417226208060054194172021994326550000000000000)
      constant := (40085674591201003760987196192971120923674119362494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63602347206245970987/25000000000000000000)
  centralHi := (254409388824983883949/100000000000000000000)
  directionLo := (129627858706781406189/50000000000000000000)
  directionHi := (259255717413562812379/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree028.table
  base := (-10957596574718276369039214099369672470791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-23481496590412943162328549034029239100000000000000)
      constant := (192392858825995428677163769628421885527422549052329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree028.table
  base := (-1370050764064094810277056356218601231193/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-46973494583287089213424425691774303200000000000000)
      constant := (384963121053083567800558493762663870889443404169072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129627858706781406189/50000000000000000000)
  centralHi := (259255717413562812379/100000000000000000000)
  directionLo := (10560523994646510903/4000000000000000000)
  directionHi := (8250409370817586643/3125000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree029.table
  base := (-2261801478388684313842249895867216324829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-24209678839076267473581856930518424350000000000000)
      constant := (204906576133801835266433801218113177336430400752255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree029.table
  base := (-1413949778434296279170955200538283775769/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-48430234130701637939101303185599667450000000000000)
      constant := (410003014706243353781687198640974182871662324804976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10560523994646510903/4000000000000000000)
  centralHi := (8250409370817586643/3125000000000000000)
  directionLo := (268686260888530991403/100000000000000000000)
  directionHi := (67171565222132747851/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree030.table
  base := (-2898971197411891800496241071113108411907/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-2770873454193287976092796091889734400000000000000)
      constant := (24204613832753940313828006203474348778415435728148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree030.table
  base := (-1449784011037607331922586552388023266627/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-5542997075346242962753131186602781300000000000000)
      constant := (48431750460317096918077094805381239988313972344912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268686260888530991403/100000000000000000000)
  centralHi := (67171565222132747851/25000000000000000000)
  directionLo := (136639760574639327851/50000000000000000000)
  directionHi := (273279521149278655703/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree031.table
  base := (-11822472390526312567179811752328902352787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-25666043336402916096088472723496794850000000000000)
      constant := (231195499645363251846809491515083500750061699129053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree031.table
  base := (-11824670497587044843544165704288704002751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-51343713225530735390455058173250395950000000000000)
      constant := (462606931687718375456022840433733194011520249895138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136639760574639327851/50000000000000000000)
  centralHi := (273279521149278655703/100000000000000000000)
  directionLo := (55559368811712877993/20000000000000000000)
  directionHi := (138898422029282194983/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree032.table
  base := (-1199251801440044229392464519224749628421/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-26394225585066240407341780619985980100000000000000)
      constant := (244966554856681246696428004687220114532044114362990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree032.table
  base := (-2398908093539542544905817867960345874837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-52800452772945284116131935667075760200000000000000)
      constant := (490162654721962177820344841389639624615837511630030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55559368811712877993/20000000000000000000)
  centralHi := (138898422029282194983/50000000000000000000)
  directionLo := (141120937902759173401/50000000000000000000)
  directionHi := (282241875805518346803/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree033.table
  base := (-12109335898368523724430033803682587836311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-3013600870414396079843898724052796150000000000000)
      constant := (28794774290624508908131793505951953525686721894801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree033.table
  base := (-3027798861585800566789133492516040668157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-6028576924484425871312090351211236050000000000000)
      constant := (57616609004378988357205255419370047359163829006296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141120937902759173401/50000000000000000000)
  centralHi := (282241875805518346803/100000000000000000000)
  directionLo := (286617979805065516203/100000000000000000000)
  directionHi := (71654494951266379051/25000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree034.table
  base := (-12175860250972825226571390836179099011543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-27850590082392889029848396412964350600000000000000)
      constant := (273753216807174154343741985562171610116566804192217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree034.table
  base := (-12177568874981216753538802676572864298247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-55713931867774381567485690654726488700000000000000)
      constant := (547764363206943313657889719396211136461110543861586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286617979805065516203/100000000000000000000)
  centralHi := (71654494951266379051/25000000000000000000)
  directionLo := (290928266479653443483/100000000000000000000)
  directionHi := (72732066619913360871/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree035.table
  base := (-12194691513326736785041420864516771896353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-28578772331056213341101704309453535850000000000000)
      constant := (288765948685043981763518010292727117610977596146607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree035.table
  base := (-6098130226582384203601793134491021323219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-57170671415188930293162568148551852950000000000000)
      constant := (577804600502340399185759924991431120927489627747444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290928266479653443483/100000000000000000000)
  centralHi := (72732066619913360871/25000000000000000000)
  directionLo := (36896952390698786791/12500000000000000000)
  directionHi := (295175619125590294329/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree036.table
  base := (-1216813645079374070231773269579943070821/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-3256328286635504183595001356215857900000000000000)
      constant := (33798885116314796330121013988101930474139208402110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree036.table
  base := (-12169576232589609676848799784354095839149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-6514156773622608779871049515819690800000000000000)
      constant := (67629755251356529265721517979317503373828312804118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36896952390698786791/12500000000000000000)
  centralHi := (295175619125590294329/100000000000000000000)
  directionLo := (149681358237670037593/50000000000000000000)
  directionHi := (299362716475340075187/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree037.table
  base := (-12098243001384393215716174267116852049013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-30035136828382861963608320102431906350000000000000)
      constant := (320024205132754178965473801172535329356706981045147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree037.table
  base := (-2419912693430396217294752347895555579381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-60084150510018027744516323136202581450000000000000)
      constant := (640351826677671905830130452140704413481468569925390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149681358237670037593/50000000000000000000)
  centralHi := (299362716475340075187/100000000000000000000)
  directionLo := (75873013114353672273/25000000000000000000)
  directionHi := (303492052457414689093/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree038.table
  base := (-2397366129803059137133306366773060346987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-30763319077046186274861627998921091600000000000000)
      constant := (336267720848856632871419826234042315997853966394265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree038.table
  base := (-2997010246820960455080300454637986873721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-61540890057432576470193200630027945700000000000000)
      constant := (672854799239707695199117853359106482474107309495992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75873013114353672273/25000000000000000000)
  centralHi := (303492052457414689093/100000000000000000000)
  directionLo := (19222872097993936141/6250000000000000000)
  directionHi := (307565953567902978257/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree039.table
  base := (-11835516962194068322932168353445115395203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-3499055702856612287346103988378919650000000000000)
      constant := (39213296998005179986309026076665406807279057419973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree039.table
  base := (-2367325147846592370540644418493812328699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-6999736622760791688430008680428145550000000000000)
      constant := (78463892796507642765446582080313057853547234761090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19222872097993936141/6250000000000000000)
  centralHi := (307565953567902978257/100000000000000000000)
  directionLo := (12463463767890706367/4000000000000000000)
  directionHi := (38948324274658457397/12500000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree040.table
  base := (-5822870417482098429063850055624117398021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-32219683574372834897368243791899462100000000000000)
      constant := (369979314128050139388376824469315823888078803877398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree040.table
  base := (-2911689006551986033165882325894473416687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-64454369152261673921546955617678674200000000000000)
      constant := (740311040269501523087279744535365983068058332105224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12463463767890706367/4000000000000000000)
  centralHi := (38948324274658457397/12500000000000000000)
  directionLo := (39444501274887014787/12500000000000000000)
  directionHi := (315556010199096118297/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree041.table
  base := (-11418782882097526260780427968922951500081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-32947865823036159208621551688388647350000000000000)
      constant := (387445979097544768085903574964666806644984454695839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree041.table
  base := (-11419711903447831091081648695858740103291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-65911108699676222647223833111504038450000000000000)
      constant := (775261484745136953416664938102927604429796297639658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39444501274887014787/12500000000000000000)
  centralHi := (315556010199096118297/100000000000000000000)
  directionLo := (319476110941164667809/100000000000000000000)
  directionHi := (31947611094116466781/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree042.table
  base := (-11155783370752112775064113984465853711963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-3741783119077720391097206620541981400000000000000)
      constant := (45035452844658260226430027871298504247333599225133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree042.table
  base := (-11156633109494150838061669850744781182967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-7485316471898974596988967845036600300000000000000)
      constant := (90113909396380108574911891018815984900881477456994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319476110941164667809/100000000000000000000)
  centralHi := (31947611094116466781/10000000000000000000)
  directionLo := (323348690041278280889/100000000000000000000)
  directionHi := (32334869004127828089/10000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree043.table
  base := (-5428879006579534741721724504669374304583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-34404230320362807831128167481367017850000000000000)
      constant := (423598076050108666377577291037636593745251710943954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree043.table
  base := (-5429267429139805250872216184861793242403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-68824587794505320098577588099154766950000000000000)
      constant := (847601085071855168721832742860069051318667616146228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323348690041278280889/100000000000000000000)
  centralHi := (32334869004127828089/10000000000000000000)
  directionLo := (65435086991836408023/20000000000000000000)
  directionHi := (81793858739795510029/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree044.table
  base := (-10525611897039403991237634599015865702157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-35132412569026132142381475377856203100000000000000)
      constant := (442282510312671541107595168785382290364389748478083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree044.table
  base := (-10526321768777177415977444092484836220931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-70281327341919868824254465592980131200000000000000)
      constant := (884988246486550418119854446175473146598849130293978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65435086991836408023/20000000000000000000)
  centralHi := (81793858739795510029/25000000000000000000)
  directionLo := (33095793559008259377/10000000000000000000)
  directionHi := (330957935590082593771/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree045.table
  base := (-10160151790540856395763766192306565762561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-3984510535298828494848309252705043150000000000000)
      constant := (51263551036699038292033728471699591866444157558551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree045.table
  base := (-508040008451792060123165580691682083553/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-7970896321037157505547927009645055050000000000000)
      constant := (102576203461118243256125059763859991058898999392920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33095793559008259377/10000000000000000000)
  centralHi := (330957935590082593771/100000000000000000000)
  directionLo := (167348845991964163373/50000000000000000000)
  directionHi := (334697691983928326747/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree046.table
  base := (-9762097025060312757667176436945602549263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-36588777066352780764888091170834573600000000000000)
      constant := (480866049460890059128828101626026954528483533124897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree046.table
  base := (-9762688977999533362957687338175381388261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-73194806436748966275608220580630859700000000000000)
      constant := (962193092206721059883960439021135032559384503250518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167348845991964163373/50000000000000000000)
  centralHi := (334697691983928326747/100000000000000000000)
  directionLo := (169198060648377306871/50000000000000000000)
  directionHi := (338396121296754613743/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree047.table
  base := (-9332089131206919633355114999958527252341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-37316959315016105076141399067323758850000000000000)
      constant := (500764447474428023877691938726943735282336707866779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree047.table
  base := (-1166578667548836147819204447344833169369/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-74651545984163515001285098074456223950000000000000)
      constant := (1002009363597323731069001080711572066573008061739376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169198060648377306871/50000000000000000000)
  centralHi := (338396121296754613743/100000000000000000000)
  directionLo := (534460256352270477/156250000000000000)
  directionHi := (342054564065453105281/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree048.table
  base := (-8870700379422034945761299254461239099357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-4227237951519936598599411884868104900000000000000)
      constant := (57896317346294715399975420460976102171972918464987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree048.table
  base := (-8871193166197069734490320787145980705829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-8456476170175340414106886174253509800000000000000)
      constant := (115848227909758577329321532143387526253675352819878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (534460256352270477/156250000000000000)
  centralHi := (342054564065453105281/100000000000000000000)
  directionLo := (69134857976950083301/20000000000000000000)
  directionHi := (172837144942375208253/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree049.table
  base := (-8378441356644050172749168569728941413027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-38773323812342753698648014860302129350000000000000)
      constant := (541773010173552771843088913018405047261613696145613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree049.table
  base := (-65460083641945461323070406614623703803/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-77565025078992612452638853062106952450000000000000)
      constant := (1084066624899462492147744243631370831282858721128192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69134857976950083301/20000000000000000000)
  centralHi := (172837144942375208253/50000000000000000000)
  directionLo := (349256502554563421051/100000000000000000000)
  directionHi := (87314125638640855263/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree050.table
  base := (-7855767693272903408897473191321354561367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-39501506061006078009901322756791314600000000000000)
      constant := (562882672977175729860735537266374361206701244266073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree050.table
  base := (-7856177277598210809626252607740037725361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-79021764626407161178315730555932316700000000000000)
      constant := (1126306611721598483930854360558245440959275540320318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349256502554563421051/100000000000000000000)
  centralHi := (87314125638640855263/25000000000000000000)
  directionLo := (352802344756897933503/100000000000000000000)
  directionHi := (5512536636826530211/1562500000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree051.table
  base := (-3651543020025028491026996464032830965413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-4469965367741044702350514517031166650000000000000)
      constant := (64932848144561821829143463023337279614718578528166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree051.table
  base := (-3651729620003676400331131054681278606229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-8942056019313523322665845338861964550000000000000)
      constant := (129928176611537852053202300025738191603133598185356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352802344756897933503/100000000000000000000)
  centralHi := (5512536636826530211/1562500000000000000)
  directionLo := (35631290231380110399/10000000000000000000)
  directionHi := (356312902313801103991/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree052.table
  base := (-1680189845479092292137063454008658602277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-40957870558332726632407938549769685100000000000000)
      constant := (606311702600042733829415747289590039363925408065452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree052.table
  base := (-1344219861564948772118989887368132190977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-81935243721236258629669485543583045200000000000000)
      constant := (1213207181436909475065914128796415474814749858116630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35631290231380110399/10000000000000000000)
  centralHi := (356312902313801103991/100000000000000000000)
  directionLo := (7195784161426846729/2000000000000000000)
  directionHi := (359789208071342336451/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree053.table
  base := (-61091117651082157671684232841331327373/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-41686052806996050943661246446258870350000000000000)
      constant := (628630712554901552030348619510867287706983604198700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree053.table
  base := (-6109421276313544467594129868795193442457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-83391983268650807355346363037408409450000000000000)
      constant := (1257867051143064398175679537024554789372327537267566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7195784161426846729/2000000000000000000)
  centralHi := (359789208071342336451/100000000000000000000)
  directionLo := (90808061362250134069/25000000000000000000)
  directionHi := (363232245449000536277/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree054.table
  base := (-2734216252213289368454960334453738149813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-4712692783962152806101617149194228400000000000000)
      constant := (72372501431882007603071337569713752804685578488966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree054.table
  base := (-2734357113849130396486409900656146980049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-9427635868451706231224804503470419300000000000000)
      constant := (144814766478503346865135735777836453571817348695836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90808061362250134069/25000000000000000000)
  centralHi := (363232245449000536277/100000000000000000000)
  directionLo := (73328590337805423309/20000000000000000000)
  directionHi := (183321475844513558273/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree055.table
  base := (-4798979929537894931328109090585746879799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-43142417304322699566167862239237240850000000000000)
      constant := (674476969412056052890047097157880264801329260085881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree055.table
  base := (-191969451054140236326297623822741462259/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-86305462363479904806700118025059137950000000000000)
      constant := (1349604454782772112333161471199120285851291704531050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73328590337805423309/20000000000000000000)
  centralHi := (183321475844513558273/50000000000000000000)
  directionLo := (370022220836210826433/100000000000000000000)
  directionHi := (185011110418105413217/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree056.table
  base := (-4100984722151489028055986280878347014441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-43870599552986023877421170135726426100000000000000)
      constant := (698003962307328818365535460755380698410481608976679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree056.table
  base := (-1025304476226202434201027194305558892113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-87762201910894453532376995518884502200000000000000)
      constant := (1396681481132757059715097782699088347425144247952376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370022220836210826433/100000000000000000000)
  centralHi := (185011110418105413217/50000000000000000000)
  directionLo := (186685453237444879127/50000000000000000000)
  directionHi := (74674181294977951651/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree057.table
  base := (-3374652889810290666271215369354614927563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-4955420200183260909852719781357290150000000000000)
      constant := (80214820507369339701980403362023045894283123644733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree057.table
  base := (-42185811712274649253407601521339076759/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-9913215717589889139783763668078874050000000000000)
      constant := (160507084837186691747960279497225247278024788731040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186685453237444879127/50000000000000000000)
  centralHi := (74674181294977951651/20000000000000000000)
  directionLo := (188344912123476391069/50000000000000000000)
  directionHi := (376689824246952782139/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree058.table
  base := (-327521052087367285748342935179849790677/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-45326964050312672499927785928704796600000000000000)
      constant := (746265140622195433956915342905131424739805832927704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree058.table
  base := (-104814447481274165874667281048097167267/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-90675681005723550983730750506535230700000000000000)
      constant := (1493251111031182617328713761519131602049974927408650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188344912123476391069/50000000000000000000)
  centralHi := (376689824246952782139/100000000000000000000)
  directionLo := (379979754171876211919/100000000000000000000)
  directionHi := (4749746927148452649/1250000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree059.table
  base := (-73507825088282943424042127101137484933/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-46055146298975996811181093825193981850000000000000)
      constant := (770999145119977656175707176688921376092852737590675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree059.table
  base := (-1837870822930346998785553856420266271953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-92132420553138099709407628000360594950000000000000)
      constant := (1542743353074929425858574665368802289767473787926014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (379979754171876211919/100000000000000000000)
  centralHi := (4749746927148452649/1250000000000000000)
  directionLo := (191620721393746179329/50000000000000000000)
  directionHi := (383241442787492358659/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree060.table
  base := (-1027381293893710514886709181937181617757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-5198147616404369013603822413520351900000000000000)
      constant := (88459480202405246200510468699141686087805490839387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree060.table
  base := (-64221279565036822452637249598915317743/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-10398795566728072048342722832687328800000000000000)
      constant := (177004481926630318887249140629551041442653297315616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191620721393746179329/50000000000000000000)
  centralHi := (383241442787492358659/100000000000000000000)
  directionLo := (386475605128134937691/100000000000000000000)
  directionHi := (96618901282033734423/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree061.table
  base := (-94678258951677854224374934746153353813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-47511510796302645433687709618172352350000000000000)
      constant := (821673602629378443027461189071163531001153666552694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree061.table
  base := (-7580044230747252300801011571274565291/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-95045899647967197160761382988011323450000000000000)
      constant := (1644141927767658145800128425362977627779999109891450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386475605128134937691/100000000000000000000)
  centralHi := (96618901282033734423/25000000000000000000)
  directionLo := (194841463277505040839/50000000000000000000)
  directionHi := (389682926555010081679/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree062.table
  base := (338130796639908560729800947482163581501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-48239693044965969744941017514661537600000000000000)
      constant := (847613926714068190780403811681679731039657763862362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree062.table
  base := (67613029349676395544923451660556195947/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-96502639195381745886438260481836687700000000000000)
      constant := (1696048002827519075894564053329888684215366474058140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194841463277505040839/50000000000000000000)
  centralHi := (389682926555010081679/100000000000000000000)
  directionLo := (39286406445206550963/10000000000000000000)
  directionHi := (392864064452065509631/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree063.table
  base := (784684214321538471757337082401113017723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-5440875032625477117354925045683413650000000000000)
      constant := (97106248859739054121875870021870760933770178941414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree063.table
  base := (1569249225964975303063136364316896548287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-10884375415866254956901681997295783550000000000000)
      constant := (194306494884412061088523004198505405536622048334766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39286406445206550963/10000000000000000000)
  centralHi := (392864064452065509631/100000000000000000000)
  directionLo := (396019649799244158863/100000000000000000000)
  directionHi := (24751228112452759929/6250000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree064.table
  base := (31123381717346531115860212459061021419/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-49696057542292618367447633307639908100000000000000)
      constant := (900700493159009773381814186441388709753216426987120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree064.table
  base := (2489762343910234083186044432239460410047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-99416118290210843337792015469487416200000000000000)
      constant := (1802273184189067783276608252165852630872805684810014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396019649799244158863/100000000000000000000)
  centralHi := (24751228112452759929/6250000000000000000)
  directionLo := (79830057726757353383/20000000000000000000)
  directionHi := (99787572158446691729/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree065.table
  base := (3437684436146538446241394344912636030663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-50424239790955942678700941204129093350000000000000)
      constant := (927846643614404248179577748315378108662526388308503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree065.table
  base := (687517251714077946595496756377141640163/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-100872857837625392063468892963312780450000000000000)
      constant := (1856592106886400530630807299765426466744041838780030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79830057726757353383/20000000000000000000)
  centralHi := (99787572158446691729/25000000000000000000)
  directionLo := (402256563409168734507/100000000000000000000)
  directionHi := (100564140852292183627/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree066.table
  base := (4412735544146455818313108989391670642237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-5683602448846585221106027677846475400000000000000)
      constant := (106154961373818638614236475447321095315639358892933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree066.table
  base := (1103161618987075001788217663179043790547/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-11369955265004437865460641161904238300000000000000)
      constant := (212412793851435605315171621154595618700952319133784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402256563409168734507/100000000000000000000)
  centralHi := (100564140852292183627/25000000000000000000)
  directionLo := (16213561370412060739/4000000000000000000)
  directionHi := (101334758565075379619/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree067.table
  base := (5414957232494009634387273475181548398913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-51880604288282591301207556997107463850000000000000)
      constant := (983344484799875393534544351988026766958183440336753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree067.table
  base := (8460744447961334543597784512179741811/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-103786336932454489514822647950963508950000000000000)
      constant := (1967642228383213591678885108141152029337169118132480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16213561370412060739/4000000000000000000)
  centralHi := (101334758565075379619/25000000000000000000)
  directionLo := (81679648036556374353/20000000000000000000)
  directionHi := (204199120091390935883/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree068.table
  base := (6444289975275239907875662861361980441601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-52608786536945915612460864893596649100000000000000)
      constant := (1011696110001400686729545681242370366526309046559281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree068.table
  base := (1288843343553924646723483342965047622683/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-105243076479869038240499525444788873200000000000000)
      constant := (2024373296283931066701548293503846813158000390541230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81679648036556374353/20000000000000000000)
  centralHi := (204199120091390935883/50000000000000000000)
  directionLo := (205717350066609896307/50000000000000000000)
  directionHi := (82286940026643958523/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree069.table
  base := (7500680591505531792441720514742927281667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-5926329865067693324857130310009537150000000000000)
      constant := (115605500038351305928621311684256035591241387439803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree069.table
  base := (7500614174907927766695350076719958544463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-11855535114142620774019600326512693050000000000000)
      constant := (231323143687424777929899122598005255847421364534734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205717350066609896307/50000000000000000000)
  centralHi := (82286940026643958523/20000000000000000000)
  directionLo := (103612228514251574371/25000000000000000000)
  directionHi := (82889782811401259497/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree070.table
  base := (536505098009910887031756618971483484379/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-54065151034272564234967480686575019600000000000000)
      constant := (1069604631151482493301700225232577433305204039249584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree070.table
  base := (4292010683069627502514457591076376960991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-108156555574698135691853280432439601700000000000000)
      constant := (2140247169795965167669247478561708050538433218295484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103612228514251574371/25000000000000000000)
  centralHi := (82889782811401259497/20000000000000000000)
  directionLo := (417441363849284937517/100000000000000000000)
  directionHi := (208720681924642468759/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree071.table
  base := (4847225227782313968006836715273660543217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73159110000000000000000000000000000000000000000
      center := (420687513)
      previous := (0)
      next := (369430875)
      square := (9631286257274649412320477750799500000000000000)
      linear := (-771737088492054768256630825113580350000000000000)
      constant := (15481147610855556273075690373170882826106774451374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree071.table
  base := (9694395897635006417162133937284741187571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 146318220000000000000000000000000000000000000000
      center := (841591701)
      previous := (0)
      next := (738645075)
      square := (19262572514549298824640955501599000000000000000)
      linear := (-1543849227072009639683523351074154450000000000000)
      constant := (30977322282677913168933407390270107305747607484362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417441363849284937517/100000000000000000000)
  centralHi := (208720681924642468759/50000000000000000000)
  directionLo := (210206257127178777781/50000000000000000000)
  directionHi := (420412514254357555563/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree072.table
  base := (2166349865482389367901282510180393860781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-6169057281288801428608232942172598900000000000000)
      constant := (125457780922543971976776637069983233375311018467145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree072.table
  base := (5415849947064807637996919295618942713359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-12341114963280803682578559491121147800000000000000)
      constant := (251037376740249864568164521620591541871625484359324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210206257127178777781/50000000000000000000)
  centralHi := (420412514254357555563/100000000000000000000)
  directionLo := (423362813708277520203/100000000000000000000)
  directionHi := (105840703427069380051/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree073.table
  base := (11995944298424916747453284394248518836003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-56249697780262537168727404376042575350000000000000)
      constant := (1159480257346918347651659765871335432829957529605043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree073.table
  base := (11995899516987587394881351464446868054273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-112526774216941781868883912913915694450000000000000)
      constant := (2320086660418732725585583467133981957645385230153826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423362813708277520203/100000000000000000000)
  centralHi := (105840703427069380051/25000000000000000000)
  directionLo := (2664329344555974787/625000000000000000)
  directionHi := (426292695128955965921/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree074.table
  base := (1648375636692508696128440225282387610361/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-56977880028925861479980712272531760600000000000000)
      constant := (1190242151777045735485212286528280156625945332198728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree074.table
  base := (13186964533739783762978754242148744734613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-113983513764356330594560790407741058700000000000000)
      constant := (2381640659932300066973083540574373113576600920496906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2664329344555974787/625000000000000000)
  centralHi := (426292695128955965921/100000000000000000000)
  directionLo := (85840515331544532579/20000000000000000000)
  directionHi := (26825161041107666431/6250000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree075.table
  base := (14404904663066979313147015060781093662431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-6411784697509909532359335574335660650000000000000)
      constant := (135711744171429538018927267389672663805350850668279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree075.table
  base := (14404867933577675102055804676188211046723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-12826694812418986591137518655729602550000000000000)
      constant := (271555373460279943271760036106163697712282778663414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85840515331544532579/20000000000000000000)
  centralHi := (26825161041107666431/6250000000000000000)
  directionLo := (432092862355938020631/100000000000000000000)
  directionHi := (54011607794492252579/12500000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree076.table
  base := (7824809419457156940491431061015951824511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-58434244526252510102487328065510131100000000000000)
      constant := (1252970882090754696696099368743396926384234233421982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree076.table
  base := (15649585583887516184795747184574388605267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-116896992859185428045914545395391787200000000000000)
      constant := (2507159738978999274244572990601465472538007745459654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432092862355938020631/100000000000000000000)
  centralHi := (54011607794492252579/12500000000000000000)
  directionLo := (217481971429971007103/50000000000000000000)
  directionHi := (434963942859942014207/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree077.table
  base := (338422520549801732439251403900001172887/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-59162426774915834413740635961999316350000000000000)
      constant := (1284937694204359701792411044839499124362866012952350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree077.table
  base := (16921095923435101199789430331244976007727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-118353732406599976771591422889217151450000000000000)
      constant := (2571124771042649410387464334130520626731717578290174) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217481971429971007103/50000000000000000000)
  centralHi := (434963942859942014207/100000000000000000000)
  directionLo := (218908097998672837389/50000000000000000000)
  directionHi := (437816195997345674779/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree078.table
  base := (1821940693535657482769532272846651601259/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-6654512113731017636110438206498722400000000000000)
      constant := (146367347095788517306610504103425704522955668409310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree078.table
  base := (9109689844141560976052490907601082498279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-13312274661557169499696477820338057300000000000000)
      constant := (292877048591216475141681117672284298549093664008444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218908097998672837389/50000000000000000000)
  centralHi := (437816195997345674779/100000000000000000000)
  directionLo := (440649987367417842517/100000000000000000000)
  directionHi := (220324993683708921259/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree079.table
  base := (1221527770258798538224514790874837667357/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-60618791272242483036247251754977686850000000000000)
      constant := (1350076162109842969268386583307010667553962489969872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree079.table
  base := (19544419666943488136795954276366068385883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-121267211501429074222945177876867879950000000000000)
      constant := (2701465719933580335342775113612920477297431783186646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440649987367417842517/100000000000000000000)
  centralHi := (220324993683708921259/50000000000000000000)
  directionLo := (443465670888091184983/100000000000000000000)
  directionHi := (55433208861011398123/12500000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree080.table
  base := (20896222791576270149166346666041171986509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-61346973520905807347500559651466872100000000000000)
      constant := (1383247800947204308153782481590716397497818506173629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree080.table
  base := (5224050120410472976538078626059032412663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-122723951048843622948622055370693244200000000000000)
      constant := (2767841602905200781159735859555546577946225619604024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443465670888091184983/100000000000000000000)
  centralHi := (55433208861011398123/12500000000000000000)
  directionLo := (223131794655952217831/50000000000000000000)
  directionHi := (446263589311904435663/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree081.table
  base := (1392170535992930810951033432161076995953/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-6897239529952125739861540838661784150000000000000)
      constant := (157424559247322852261442071281807658732248764588432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree081.table
  base := (11137354196453190809920565643466522041521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-13797854510695352408255436984946512050000000000000)
      constant := (315002341329158949758671241610230463064272431904356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223131794655952217831/50000000000000000000)
  centralHi := (446263589311904435663/100000000000000000000)
  directionLo := (449044074713010112779/100000000000000000000)
  directionHi := (22452203735650505639/5000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree082.table
  base := (23679949381021188121240006524847512574267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-62803338018232455970007175444445242600000000000000)
      constant := (1450795852559012970013240429354264241605094996618827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree082.table
  base := (1479995695311885449909181019802513316071/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-125637430143672720399975810358343972700000000000000)
      constant := (2903004114352495156932345420065346966804980374507232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449044074713010112779/100000000000000000000)
  centralHi := (22452203735650505639/5000000000000000000)
  directionLo := (451807448947206612493/100000000000000000000)
  directionHi := (225903724473603306247/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree083.table
  base := (25111874220512989456608636191952451792889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-63531520266895780281260483340934427850000000000000)
      constant := (1485172253239829591144042673587950329258198211338409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree083.table
  base := (25111857709905233851693690302529577958511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-127094169691087269125652687852169336950000000000000)
      constant := (2971790718681197577003664333147708530584732999929982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451807448947206612493/100000000000000000000)
  centralHi := (225903724473603306247/50000000000000000000)
  directionLo := (454554024086798741951/100000000000000000000)
  directionHi := (7102406626356230343/1562500000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree084.table
  base := (1328524663899066307614494131899378261457/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-7139966946173233843612643470824845900000000000000)
      constant := (168883358907715099721465632864747325876548764678260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree084.table
  base := (13285239174040539136791901979277097079199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-14283434359833535316814396149554966800000000000000)
      constant := (337931208307573583011535766722890885570646385913564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454554024086798741951/100000000000000000000)
  centralHi := (7102406626356230343/1562500000000000000)
  directionLo := (22864205141597493997/5000000000000000000)
  directionHi := (457284102831949879941/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree085.table
  base := (28055797782495115797530019799427894412457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-64987884764222428903767099133912798350000000000000)
      constant := (1555129778791949954851081977039852897583414221936217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree085.table
  base := (28055784283875102320196432084724752320487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-130007648785916366577006442839820065450000000000000)
      constant := (3111774573517507883824898284335280337281894144349294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22864205141597493997/5000000000000000000)
  centralHi := (457284102831949879941/100000000000000000000)
  directionLo := (22999898945003030901/5000000000000000000)
  directionHi := (459997978900060618021/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree086.table
  base := (5913555979443529224383051187418671575351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-65716067012885753215020407030401983600000000000000)
      constant := (1590710895036686169714006695778248478424141686965155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree086.table
  base := (14783883847175331434169835813811255416597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-131464388333330915302683320333645429700000000000000)
      constant := (3182971806802303517125512656825855186193510007262228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22999898945003030901/5000000000000000000)
  centralHi := (459997978900060618021/100000000000000000000)
  directionLo := (46269593739459169243/10000000000000000000)
  directionHi := (462695937394591692431/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree087.table
  base := (3110643261991507266827902982461561099617/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-7382694362394341947363746102987907650000000000000)
      constant := (180743730585164049996463911881803688597067852813530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree087.table
  base := (31106421589907939504904219314988692121771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-14769014208971718225373355314163421550000000000000)
      constant := (361663618595704215215109745638228805655606938596678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46269593739459169243/10000000000000000000)
  centralHi := (462695937394591692431/100000000000000000000)
  directionLo := (58172281894330269201/12500000000000000000)
  directionHi := (465378255154642153609/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree088.table
  base := (32671749694064271794467673914544096922301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-67172431510212401837527022823380354100000000000000)
      constant := (1663077816231496985331020072826654759324783890215981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree088.table
  base := (261373917804030654440781412274027689539/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-134377867428160012754037075321296158200000000000000)
      constant := (3327776848706889652286521685884788547440602451764750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58172281894330269201/12500000000000000000)
  centralHi := (465378255154642153609/100000000000000000000)
  directionLo := (23402260054324802197/5000000000000000000)
  directionHi := (468045201086496043941/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree089.table
  base := (2141482845589395893735583556745157084037/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-67900613758875726148780330719869539350000000000000)
      constant := (1699863615028013840201351571556376856535549665635152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree089.table
  base := (4282964565166498081147783125199779226193/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-135834606975574561479713952815121522450000000000000)
      constant := (3401384645042324593013878360292817846471334709350928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23402260054324802197/5000000000000000000)
  centralHi := (468045201086496043941/100000000000000000000)
  directionLo := (58837129559782685069/12500000000000000000)
  directionHi := (470697036478261480553/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree090.table
  base := (35882355131104502150583639231112407391567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-7625421778615450051114848735150969400000000000000)
      constant := (193005663229058127974407830075776172380171520988903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree090.table
  base := (35882346991954500781866124599868400053121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-15254594058109901133932314478771876300000000000000)
      constant := (386199550132052658431644853449227407186182894240978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58837129559782685069/12500000000000000000)
  centralHi := (470697036478261480553/100000000000000000000)
  directionLo := (94666803059728835489/20000000000000000000)
  directionHi := (236667007649322088723/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree091.table
  base := (938190850902524705066628224981751902683/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-69356978256202374771286946512847909850000000000000)
      constant := (1774639876013817636312107454145235630621520949364920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree091.table
  base := (234547666768653022993093850555923303131/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-138748086070403658931067707802772250950000000000000)
      constant := (3551010762517856121474950871632692489072481521987520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94666803059728835489/20000000000000000000)
  centralHi := (236667007649322088723/50000000000000000000)
  directionLo := (475956384480822382799/100000000000000000000)
  directionHi := (1189890961202055957/250000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree092.table
  base := (39199558256707257856501469323717284942017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-70085160504865699082540254409337095100000000000000)
      constant := (1812630333813561044061936366040476426251617993806577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree092.table
  base := (39199551614514642141570979803144074161539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-140204825617818207656744585296597615200000000000000)
      constant := (3627029074895907230430492354452752644627537090478118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475956384480822382799/100000000000000000000)
  centralHi := (1189890961202055957/250000000000000000)
  directionLo := (47856438419232131873/10000000000000000000)
  directionHi := (478564384192321318731/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree093.table
  base := (40898124229868224415724924366212325888139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-7868149194836558154865951367314031150000000000000)
      constant := (205669148956666311994559507720284197813399342494851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree093.table
  base := (8179623646114602610666924844267976585179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-15740173907248084042491273643380331050000000000000)
      constant := (411538987180941387539807967599165637728019441442110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47856438419232131873/10000000000000000000)
  centralHi := (478564384192321318731/100000000000000000000)
  directionLo := (4811582480917219237/1000000000000000000)
  directionHi := (481158248091721923701/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree094.table
  base := (42623328771961515862501328857462807511851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-71541525002192347705046870202315465600000000000000)
      constant := (1889815894749456974857718137694749866850245168649531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree094.table
  base := (520304240160687496049727932127778239/122070312500000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-143118304712647305108098340284248343700000000000000)
      constant := (3781476188414892004529563048684325142987484326594560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4811582480917219237/1000000000000000000)
  centralHi := (481158248091721923701/100000000000000000000)
  directionLo := (96747640714596100287/20000000000000000000)
  directionHi := (120934550893245125359/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree095.table
  base := (22187584519194745386768441465287245622543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-72269707250855672016300178098804650850000000000000)
      constant := (1929010994754373099324130186242913969040422313797566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree095.table
  base := (11093791036479390157651325157646016706599/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-144575044260061853833775217778073707950000000000000)
      constant := (3859904983306084442348958757982003313866260113319352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96747640714596100287/20000000000000000000)
  centralHi := (120934550893245125359/25000000000000000000)
  directionLo := (486304471998082315497/100000000000000000000)
  directionHi := (243152235999041157749/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree096.table
  base := (23076821243737445324763058521883334205889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-8110876611057666258617053999477092900000000000000)
      constant := (218734182144946952640335881817934190801284735909202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree096.table
  base := (46153638070043994673435205691767188070097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-16225753756386266951050232807988785800000000000000)
      constant := (437681918518566235393643098535269439650114997855346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486304471998082315497/100000000000000000000)
  centralHi := (243152235999041157749/50000000000000000000)
  directionLo := (24442863445935141103/5000000000000000000)
  directionHi := (488857268918702822061/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree097.table
  base := (4795874684820169646230236473982684043269/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-73726071748182320638806793891783021350000000000000)
      constant := (2008605827220272271864705846477527823077440068671890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree097.table
  base := (47958742860119529937017677979949430647071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-147488523354890951285128972765724436450000000000000)
      constant := (4019173036143639749971659634463610362479904426228702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24442863445935141103/5000000000000000000)
  centralHi := (488857268918702822061/100000000000000000000)
  directionLo := (491396804287504732621/100000000000000000000)
  directionHi := (245698402143752366311/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree098.table
  base := (24895240045695803166873453712739573395953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-74454253996845644950060101788272206600000000000000)
      constant := (2049005557447606755592506009712240237665271906961986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree098.table
  base := (9958095298262068173666054774810837929451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-148945262902305500010805850259549800700000000000000)
      constant := (4100012289632197760465541807968686919222874334351310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491396804287504732621/100000000000000000000)
  centralHi := (245698402143752366311/50000000000000000000)
  directionLo := (61740410332457138363/12500000000000000000)
  directionHi := (98784656531931421381/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree099.table
  base := (51648840403950191761511635707173692925533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-8353604027278774362368156631640154650000000000000)
      constant := (232200758782750107147396826650255581753794618104997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree099.table
  base := (25824418577229672231908390465141674215921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-16711333605524449859609191972597240550000000000000)
      constant := (464628336139256708557508772971350450530194675622756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61740410332457138363/12500000000000000000)
  centralHi := (98784656531931421381/20000000000000000000)
  directionLo := (99287380677024778131/20000000000000000000)
  directionHi := (15513653230785121583/3125000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree100.table
  base := (53533826165855777797967226681712823312609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-75910618494172293572566717581250577100000000000000)
      constant := (2131009641170217556235769345995853865346877856147729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree100.table
  base := (2676691161655626273763241535092451413907/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-151858741997134597462159605247200529200000000000000)
      constant := (4264101241327709212644674908058872782487348478946680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99287380677024778131/20000000000000000000)
  centralHi := (15513653230785121583/3125000000000000000)
  directionLo := (124734465198058364661/25000000000000000000)
  directionHi := (99787572158446691729/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree101.table
  base := (55445435929598924643626589071359491481007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-76638800742835617883820025477739762350000000000000)
      constant := (2172613993072127164760563444356888289902551683568767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree101.table
  base := (55445433282992504546159041159225356375763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-153315481544549146187836482741025893450000000000000)
      constant := (4347350936354993190477488121600463588979372782443206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124734465198058364661/25000000000000000000)
  centralHi := (99787572158446691729/20000000000000000000)
  directionLo := (250713172181503775749/50000000000000000000)
  directionHi := (501426344363007551499/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree102.table
  base := (57383668401811507686183142305218819984499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-8596331443499882466119259263803216400000000000000)
      constant := (246068876008740666390890564346140309486082748946091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree102.table
  base := (57383666013658637051943942110170099062767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-17196913454662632768168151137205695300000000000000)
      constant := (492378234332730662860276019118822632226258102619406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250713172181503775749/50000000000000000000)
  centralHi := (501426344363007551499/100000000000000000000)
  directionLo := (503902538900697280711/100000000000000000000)
  directionHi := (62987817362587160089/12500000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree103.table
  base := (59348522426852196139755654555613863824991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-78095165240162266506326641270718132850000000000000)
      constant := (2257027313589559646707598482718840069252042514957871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree103.table
  base := (29674260136060354843197410211642952159641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-156228960639378243639190237728676621950000000000000)
      constant := (4516260758048662861052114543353376610370347342818084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503902538900697280711/100000000000000000000)
  centralHi := (62987817362587160089/12500000000000000000)
  directionLo := (101273324937989083007/20000000000000000000)
  directionHi := (126591656172486353759/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree104.table
  base := (3066999848606998541549378215102993217097/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-78823347488825590817579949167207318100000000000000)
      constant := (2299836281068454882933442172717777868378037169121140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree104.table
  base := (61339995028198120160908981807299151294137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-157685700186792792364867115222501986200000000000000)
      constant := (4601920882447041113168065700589468794056568638160594) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101273324937989083007/20000000000000000000)
  centralHi := (126591656172486353759/25000000000000000000)
  directionLo := (63602347206245970987/12500000000000000000)
  directionHi := (508818777649967767897/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree105.table
  base := (63358091115049515269828333219451202961137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-8839058859720990569870361895966278150000000000000)
      constant := (260338531781790303596510573146220921889491071923033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree105.table
  base := (61873134142029881429323314860445847687/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-17682493303800815676727110301814150050000000000000)
      constant := (520931609025943362693225425391792480421779886621184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63602347206245970987/12500000000000000000)
  centralHi := (508818777649967767897/100000000000000000000)
  directionLo := (102251833896224402193/20000000000000000000)
  directionHi := (255629584740561005483/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree106.table
  base := (654028040312021431279077813038017929979/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-80279711986152239440086564960185688600000000000000)
      constant := (2386658828064326436950313055664088283399127230669900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree106.table
  base := (32701401224715169624133477256455239004231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-160599179281621889816220870210152714700000000000000)
      constant := (4775651553553640110487707699925879919459485863921244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102251833896224402193/20000000000000000000)
  centralHi := (255629584740561005483/50000000000000000000)
  directionLo := (51368796780520949009/10000000000000000000)
  directionHi := (513687967805209490091/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree107.table
  base := (67474134984003641697712323035735655476219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48544830000000000000000000000000000000000000000
      center := (279147789)
      previous := (0)
      next := (245136375)
      square := (6390853497817758021259382432773500000000000000)
      linear := (-757083123689865081788223110810045550000000000000)
      constant := (22716564549256888782668092866659646200753162039777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree107.table
  base := (4217133347334944416019154459306314041583/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 97089660000000000000000000000000000000000000000
      center := (558439353)
      previous := (0)
      next := (490128975)
      square := (12781706995635516042518764865547000000000000000)
      linear := (-1514541297467630266746707922467084850000000000000)
      constant := (45455346716300205684028292423570285057715830930848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51368796780520949009/10000000000000000000)
  centralHi := (513687967805209490091/100000000000000000000)
  directionLo := (516105336299834476853/100000000000000000000)
  directionHi := (258052668149917238427/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree108.table
  base := (13914416663059247998501677618783682914721/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-9081786275942098673621464528129339900000000000000)
      constant := (275009724645858671080311525317496454991332599574445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree108.table
  base := (34786041014338862346416390392868361765471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-18168073152938998585286069466422604800000000000000)
      constant := (550288457313652862709003917418484749406369421486556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516105336299834476853/100000000000000000000)
  centralHi := (258052668149917238427/50000000000000000000)
  directionLo := (518511434827125624757/100000000000000000000)
  directionHi := (259255717413562812379/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree109.table
  base := (71696648437006053018077169445914300963047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-82464258732142212373846488649653244350000000000000)
      constant := (2519904172885586226395288667257687469408823495998007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree109.table
  base := (35848323638384687014705214486233668637753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-164969397923865535993251502691628807450000000000000)
      constant := (5042273604480489016858036222213128043258495981387172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518511434827125624757/100000000000000000000)
  centralHi := (259255717413562812379/50000000000000000000)
  directionLo := (520906419557106097297/100000000000000000000)
  directionHi := (260453209778553048649/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree110.table
  base := (36923914911839995047668374567608804734177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-83192440980805536685099796546142429600000000000000)
      constant := (2565122359716125728491041160916224336626729697815074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree110.table
  base := (36923914388749484819698774557733142610231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-166426137471280084718928380185454171700000000000000)
      constant := (5132754564072459121433999814922600501709139182665244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (520906419557106097297/100000000000000000000)
  centralHi := (260453209778553048649/50000000000000000000)
  directionLo := (261645221542990894987/50000000000000000000)
  directionHi := (20931617723439271599/4000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree111.table
  base := (19006406751454351366813178529037835089129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-9324513692163206777372567160292401650000000000000)
      constant := (290082453562274886150576757795415606019484170239044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree111.table
  base := (1900640651563947205665335830641830515479/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-18653653002077181493845028631031059550000000000000)
      constant := (580448777123586586721373045284061842800947866952880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261645221542990894987/50000000000000000000)
  centralHi := (20931617723439271599/4000000000000000000)
  directionLo := (262831827274800591393/50000000000000000000)
  directionHi := (525663654549601182787/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree112.table
  base := (3911501978195592859851126228524463070393/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-84648805478132185307606412339120800100000000000000)
      constant := (2656763339700726869675059279567464772267010330692660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree112.table
  base := (78230038713517615719763132990005803671541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-169339616566109182170282135173104900200000000000000)
      constant := (5316126894165261114862395507596644597978514340816842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262831827274800591393/50000000000000000000)
  centralHi := (525663654549601182787/100000000000000000000)
  directionLo := (528026199732325545151/100000000000000000000)
  directionHi := (8250409370817586643/1562500000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree113.table
  base := (80461067123127353681235539853439091133367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-85376987726795509618859720235609985350000000000000)
      constant := (2703186132442183471904768271560267201816584749265927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree113.table
  base := (80461066356516775820810916743693275878623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-170796356113523730895959012666930264450000000000000)
      constant := (5409018263843015233686694792992397591968581279218526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528026199732325545151/100000000000000000000)
  centralHi := (8250409370817586643/1562500000000000000)
  directionLo := (530378221171534390659/100000000000000000000)
  directionHi := (26518911058576719533/5000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree114.table
  base := (8271870934854152042816303605428105388947/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-9567241108384314881123669792455463400000000000000)
      constant := (305556717790097239989146289770851721920127912373230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree114.table
  base := (41359354328757038155574957711535661338939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-19139232851215364402403987795639514300000000000000)
      constant := (611412566977613301472153085246613302218904052288204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530378221171534390659/100000000000000000000)
  centralHi := (26518911058576719533/5000000000000000000)
  directionLo := (532719858257978170033/100000000000000000000)
  directionHi := (266359929128989085017/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree115.table
  base := (42501482970447657677049808567941906799333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-86833352224122158241366336028588355850000000000000)
      constant := (2797236322551357904901799619538113864606868542405546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree115.table
  base := (17000593063609378522994839842495984852629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-173709835208352828347312767654580992950000000000000)
      constant := (5597211410721713861802777161393897636198444134813490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532719858257978170033/100000000000000000000)
  centralHi := (266359929128989085017/50000000000000000000)
  directionLo := (267525623666089064599/50000000000000000000)
  directionHi := (535051247332178129199/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree116.table
  base := (1091422957909941876221990766812515176643/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-87561534472785482552619643925077541100000000000000)
      constant := (2844863719624739644485205395332564592200906571270640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree116.table
  base := (21828459017860407325124683344349777829367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-175166574755767377072989645148406357200000000000000)
      constant := (5692513187335561318134382659810080085952631785935416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267525623666089064599/50000000000000000000)
  centralHi := (535051247332178129199/100000000000000000000)
  directionLo := (537372521777061982807/100000000000000000000)
  directionHi := (67171565222132747851/12500000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree117.table
  base := (89651321185320619375915844075751593526711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-9809968524605422984874772424618525150000000000000)
      constant := (321432516800768635232674274974013146407452351078799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree117.table
  base := (89651320679427737340311394217151145772049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-19624812700353547310962946960247969050000000000000)
      constant := (643179825821392499077576353681035101699438313508082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537372521777061982807/100000000000000000000)
  centralHi := (67171565222132747851/12500000000000000000)
  directionLo := (21587352484280540187/4000000000000000000)
  directionHi := (134920953026753376169/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree118.table
  base := (18403083876998114627311032826107840257691/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-89017898970112131175126259718055911600000000000000)
      constant := (2941323117187003988715166587903238062358256969632855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree118.table
  base := (92015418929112390931865618781148522977177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-178080053850596474524343400136057085700000000000000)
      constant := (5885527145671461677306580070989464951619812438781074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21587352484280540187/4000000000000000000)
  centralHi := (134920953026753376169/25000000000000000000)
  directionLo := (108397049210700852477/20000000000000000000)
  directionHi := (270992623026752131193/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree119.table
  base := (11800766380132006546487727785329584044559/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-89746081218775455486379567614545096850000000000000)
      constant := (2990155117465917684534072682603937184367273769245432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree119.table
  base := (5900383164392337975671431693814004384547/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-179536793398011023250020277629882449950000000000000)
      constant := (5983239326974738935283775932812392253631156185264224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108397049210700852477/20000000000000000000)
  centralHi := (270992623026752131193/50000000000000000000)
  directionLo := (544276948647466475597/100000000000000000000)
  directionHi := (272138474323733237799/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree120.table
  base := (48411727991539353576814424460496623964409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-10052695940826531088625875056781586900000000000000)
      constant := (337709850217236451868594389797716765997202204938562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree120.table
  base := (96823455612964087446930539964078903421113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-20110392549491730219521906124856423800000000000000)
      constant := (675750552902866786561570256718323146280635229834434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544276948647466475597/100000000000000000000)
  centralHi := (272138474323733237799/50000000000000000000)
  directionLo := (109311808459711462281/20000000000000000000)
  directionHi := (273279521149278655703/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree121.table
  base := (99267394058768176764840550858412950088307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-91202445716102104108886183407523467350000000000000)
      constant := (3089023720575531002078445003407280111086888226840067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree121.table
  base := (6204212107832206454570291339820622958751/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-182450272492840120701374032617533178450000000000000)
      constant := (6181074092966889910373471052912126676697554858829792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109311808459711462281/20000000000000000000)
  centralHi := (273279521149278655703/50000000000000000000)
  directionLo := (137207911717864201127/25000000000000000000)
  directionHi := (548831646871456804509/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree122.table
  base := (50868972566024791602603243489047469946109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-91930627964765428420139491304012652600000000000000)
      constant := (3139060323256445159845533609363535692190928970122458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree122.table
  base := (20347588966329488118202368537119069188047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-183907012040254669427050910111358542700000000000000)
      constant := (6281196677357049236050220321398921161386141822230070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137207911717864201127/25000000000000000000)
  centralHi := (548831646871456804509/100000000000000000000)
  directionLo := (34443429984958372941/6250000000000000000)
  directionHi := (551094879759333967057/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree123.table
  base := (52117554540668406181635301189637135700341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-10295423357047639192376977688944648650000000000000)
      constant := (354388717770523900405741345445066090529045963826938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree123.table
  base := (52117554405363852262914224414049545293627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-20595972398629913128080865289464878550000000000000)
      constant := (709124747685592803571922921810180511878986655085772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34443429984958372941/6250000000000000000)
  centralHi := (551094879759333967057/100000000000000000000)
  directionLo := (553348855954608497737/100000000000000000000)
  directionHi := (276674427977304248869/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree124.table
  base := (26689721449497417221635464337246405831927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-93386992462092077042646107096991023100000000000000)
      constant := (3240338130553909891481138399019993570398697524901148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree124.table
  base := (106758885554234919020017587383605805751141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-186820491135083766878404665099009271200000000000000)
      constant := (6483852248294217430814485748988685985172126270032042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553348855954608497737/100000000000000000000)
  centralHi := (276674427977304248869/50000000000000000000)
  directionLo := (555593688117128779931/100000000000000000000)
  directionHi := (138898422029282194983/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree125.table
  base := (109309275184935324386581154055516806593853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-94115174710755401353899414993480208350000000000000)
      constant := (3291579335063607015050357814732077905045433760350893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree125.table
  base := (109309274965384273492923286868944198934823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-188277230682498315604081542592834635450000000000000)
      constant := (6586385234628150025480647567413607773509656301362926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555593688117128779931/100000000000000000000)
  centralHi := (138898422029282194983/25000000000000000000)
  directionLo := (557829486639880544577/100000000000000000000)
  directionHi := (278914743319940272289/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree126.table
  base := (27971569288859140928270518308469810699133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-10538150773268747296128080321107710400000000000000)
      constant := (371469119268750287818108702858975838550369351629588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree126.table
  base := (55943138478849277018065886147359695248321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-21081552247768096036639824454073333300000000000000)
      constant := (743302409786921705875262165649877294499207819029156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (557829486639880544577/100000000000000000000)
  centralHi := (278914743319940272289/50000000000000000000)
  directionLo := (280028179856167318691/50000000000000000000)
  directionHi := (560056359712334637383/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree127.table
  base := (114489891631991197083271333657181059419191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-95571539208082049976406030786458578850000000000000)
      constant := (3395266345579089679703332547253099762159602426408071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree127.table
  base := (114489891453910256301765411541219372796687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-191190709777327413055435297580485363950000000000000)
      constant := (6793861608576383342734453136336594892241231412533694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280028179856167318691/50000000000000000000)
  centralHi := (560056359712334637383/100000000000000000000)
  directionLo := (70284301672692093329/12500000000000000000)
  directionHi := (562274413381536746633/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree128.table
  base := (7320007409084291906718557674805901485351/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (29868813423)
      previous := (0)
      next := (26229592125)
      square := (683821324266500108274753920306764500000000000000)
      linear := (-96299721456745374287659338682947764100000000000000)
      constant := (3447712151508647489903502257130328335127252737648496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree128.table
  base := (58560059192490319597834686746150092928341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10388593620000000000000000000000000000000000000000
      center := (59753010771)
      previous := (0)
      next := (52443800325)
      square := (1367642648533000216549507840613529000000000000000)
      linear := (-192647449324741961781112175074310728200000000000000)
      constant := (6898804996038692452525571634094170436591554085956884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell154.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70284301672692093329/12500000000000000000)
  centralHi := (562274413381536746633/100000000000000000000)
  directionLo := (112896750322207338721/20000000000000000000)
  directionHi := (282241875805518346803/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree129.table
  base := (59888478916815697168425033866557067798361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3318757047)
      previous := (0)
      next := (2914399125)
      square := (75980147140722234252750435589640500000000000000)
      linear := (-10780878189489855399879182953270772150000000000000)
      constant := (388951054575031662701233985494064496571760672567298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree129.table
  base := (119776957689223263414462442239195738711413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6639223419)
      previous := (0)
      next := (5827088925)
      square := (151960294281444468505500871179281000000000000000)
      linear := (-21567132096906278945198783618681788050000000000000)
      constant := (778283538933904349696883627746650810230720245699834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell154.Kernel129
