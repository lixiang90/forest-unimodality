import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell073.Parameters
import ForestUnimodality.BinomialMassData.Q5227_10302.Batch000_049
import ForestUnimodality.BinomialMassData.Q5227_10302.Batch050_099
import ForestUnimodality.BinomialMassData.Q5227_10302.Batch100_149
import ForestUnimodality.BinomialMassData.Q3493_6868.Batch000_049
import ForestUnimodality.BinomialMassData.Q3493_6868.Batch050_099
import ForestUnimodality.BinomialMassData.Q3493_6868.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree000.table
  base := (1258485605187390040460115867/20000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (126)
      previous := (63)
      next := (63)
      square := (774299914215832441044540250000000000000)
      linear := (-17002507911567299112021168000000000000)
      constant := (629242802593695020230057933500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree000.table
  base := (1258485605187390040460115867/20000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (126)
      previous := (63)
      next := (63)
      square := (774299914215832441044540250000000000000)
      linear := (-17002507911567299112021168000000000000)
      constant := (629242802593695020230057933500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree001.table
  base := (89270758680422864134632662331720752711839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-21298589530341851173716105386980818000000000000)
      constant := (9479930755253319009043984306152529207593738124156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree001.table
  base := (356434328008995083329402712981391844083621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-2372049418452047009445984524703077000000000000)
      constant := (1051416069129875997868467808590563092857638150269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12498154918677782967/25000000000000000000)
  directionHi := (49992619674711131869/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree002.table
  base := (211509143038726345259851205499036782516973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-42146054901765161601985476415630068000000000000)
      constant := (5633542839720712519999498433805186428203123731373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree002.table
  base := (6588055755992466491062421049512031621893/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-4693973930357589491620109676258202000000000000)
      constant := (623922394487685164770997441508435491848957199264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/25000000000000000000)
  centralHi := (49992619674711131869/100000000000000000000)
  directionLo := (70700240762536509997/100000000000000000000)
  directionHi := (35350120381268254999/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree003.table
  base := (132154731865676255401336070009367951773301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-6999280030354274670028316382697702000000000000)
      constant := (394968972406836945595059904473707374075399171789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree003.table
  base := (6579632560596413016061870443369307590093/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-7015898442263131973794234827813327000000000000)
      constant := (393337416728985636065958620650108194504393645540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70700240762536509997/100000000000000000000)
  centralHi := (35350120381268254999/50000000000000000000)
  directionLo := (4329487864003357981/5000000000000000000)
  directionHi := (86589757280067159621/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree004.table
  base := (87653343915316773965307354859278146254983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-83840985644611782458524218472928568000000000000)
      constant := (2411224521798853787702905561159970130232359197383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree004.table
  base := (21809187946912904620028012839389335073869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-9337822954168674455968359979368452000000000000)
      constant := (266730951753101215019034767974049919794349545364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4329487864003357981/5000000000000000000)
  centralHi := (86589757280067159621/100000000000000000000)
  directionLo := (12498154918677782967/12500000000000000000)
  directionHi := (99985239349422263737/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree005.table
  base := (61683295477898115266975521155919820825791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-104688451016035092886793589501577818000000000000)
      constant := (1769994164276943528674428134169313480426368270591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree005.table
  base := (61383321661649416694364786746971329553873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-11659747466074216938142485130923577000000000000)
      constant := (195852321887552785704152217661817735598147898697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/12500000000000000000)
  centralHi := (99985239349422263737/100000000000000000000)
  directionLo := (22357379193189502981/20000000000000000000)
  directionHi := (55893447982973757453/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree006.table
  base := (1428380790296519328575276791549580209121/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-13948435154162044812784773392247452000000000000)
      constant := (156059449233750499986475594513664293812074232608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree006.table
  base := (22745437132407793547216037305273828733503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-13981671977979759420316610282478702000000000000)
      constant := (155520464534311009601797261385176607454248251534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22357379193189502981/20000000000000000000)
  centralHi := (55893447982973757453/50000000000000000000)
  directionLo := (30614102277016354781/25000000000000000000)
  directionHi := (979651272864523353/800000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree007.table
  base := (17625783764805679552864421282324295763963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-146383381758881713743332331558876318000000000000)
      constant := (1196074512137290735760815191545502652440746500726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree007.table
  base := (701793507014235982948746513981723794103/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-16303596489885301902490735434033827000000000000)
      constant := (132558205328527755289632288021041360546665958350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30614102277016354781/25000000000000000000)
  centralHi := (979651272864523353/800000000000000000)
  directionLo := (132268039047920423511/100000000000000000000)
  directionHi := (16533504880990052939/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree008.table
  base := (13972375459856665725598409646810963032589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-167230847130305024171601702587525568000000000000)
      constant := (1081764557053269771057609213691689277524080903578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree008.table
  base := (5563853681813527329007272152693037733841/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-18625521001790844384664860585588952000000000000)
      constant := (120006708397296421718416114511047940598607899245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132268039047920423511/100000000000000000000)
  centralHi := (16533504880990052939/12500000000000000000)
  directionLo := (70700240762536509997/50000000000000000000)
  directionHi := (28280096305014603999/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree009.table
  base := (22518216422055954365571481776438993088297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-20897590277969814955541230401797202000000000000)
      constant := (114213475761962482350923412764463085194684414433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree009.table
  base := (22416805288014069074643869198513852959653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-20947445513696386866838985737144077000000000000)
      constant := (114142984995421590593331625098508964882970453117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70700240762536509997/50000000000000000000)
  centralHi := (28280096305014603999/20000000000000000000)
  directionLo := (37494464756033348901/25000000000000000000)
  directionHi := (29995571804826679121/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree010.table
  base := (18278324058401945335350231478832490154807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-208925777873151645028140444644824068000000000000)
      constant := (1016140475042254298351375435218332103611953324407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree010.table
  base := (9096652508531812816545234708049159554029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-23269370025601929349013110888699202000000000000)
      constant := (112935857902599824601734000786644459980955601162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37494464756033348901/25000000000000000000)
  centralHi := (29995571804826679121/20000000000000000000)
  directionLo := (31618108874126640633/20000000000000000000)
  directionHi := (79045272185316601583/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree011.table
  base := (7417613929976562176867678242072085288761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-229773243244574955456409815673473318000000000000)
      constant := (1036078431096271323354261037166160443743446299122) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree011.table
  base := (14761928528846021629506365995551373785293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-25591294537507471831187236040254327000000000000)
      constant := (115244891119546528519601597263535041616310655077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31618108874126640633/20000000000000000000)
  centralHi := (79045272185316601583/50000000000000000000)
  directionLo := (165806761747956045531/100000000000000000000)
  directionHi := (41451690436989011383/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree012.table
  base := (11961095671691358147986265655677055885769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-27846745401777585098297687411346952000000000000)
      constant := (120187791643246237183318076830145340009220845441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree012.table
  base := (5948344109905490466685347202261530611053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-27913219049413014313361361191809452000000000000)
      constant := (120403853078098772339583289530869661035217255434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165806761747956045531/100000000000000000000)
  centralHi := (41451690436989011383/25000000000000000000)
  directionLo := (173179514560134319241/100000000000000000000)
  directionHi := (86589757280067159621/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree013.table
  base := (9515958854346466726021970258129034408761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-271468173987421576312948557730771818000000000000)
      constant := (1149261796069092261274113948136762348789808269561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree013.table
  base := (9458706163943096560358755986057946711571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-30235143561318556795535486343364577000000000000)
      constant := (128003319292227720900668261049763227687968637819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173179514560134319241/100000000000000000000)
  centralHi := (86589757280067159621/50000000000000000000)
  directionLo := (180250953631940847027/100000000000000000000)
  directionHi := (45062738407985211757/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree014.table
  base := (740870278565698738421771186968430403807/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-292315639358844886741217928759421068000000000000)
      constant := (1236375918795246143342817113283410573865607734070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree014.table
  base := (3678747327822836927508187700798554214123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-32557068073224099277709611494919702000000000000)
      constant := (137776523952428520252753267500538908289119321894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180250953631940847027/100000000000000000000)
  centralHi := (45062738407985211757/25000000000000000000)
  directionLo := (18705525469006318131/10000000000000000000)
  directionHi := (187055254690063181311/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree015.table
  base := (55763516363619071392297037290765996387/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-34795900525585355241054144420896702000000000000)
      constant := (149040174202453927367832797576460046052255444300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree015.table
  base := (553043050816748321690078553828457483953/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-34878992585129641759883736646474827000000000000)
      constant := (149538848330694924674298592028224254579095158170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18705525469006318131/10000000000000000000)
  centralHi := (187055254690063181311/100000000000000000000)
  directionLo := (9681029171671873227/5000000000000000000)
  directionHi := (193620583433437464541/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree016.table
  base := (794581380674383986349901668920653262923/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-334010570101691507597756670816719568000000000000)
      constant := (1462998274020843427277423173262666177075683186615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree016.table
  base := (3931711069329717442601870805364303023233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-37200917097035184242057861798029952000000000000)
      constant := (163155262131967766615810110370982874735459951737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9681029171671873227/5000000000000000000)
  centralHi := (193620583433437464541/100000000000000000000)
  directionLo := (12498154918677782967/6250000000000000000)
  directionHi := (199970478698844527473/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree017.table
  base := (64080008470919146795381456972136192521/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (11567934)
      previous := (5783967)
      next := (5783967)
      square := (71087700824241360579858195812250000000000000)
      linear := (-1227882475685518401474138553098162000000000000)
      constant := (5537553374635954196487754229074860567966419560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree017.table
  base := (2526277207478821355712912468094338592663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7898633424915706731095355090250000000000000)
      linear := (-136757237401178985204954972143893000000000000)
      constant := (617724594864600858999412164362726972983755263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/6250000000000000000)
  centralHi := (199970478698844527473/100000000000000000000)
  directionLo := (20612485142016560701/10000000000000000000)
  directionHi := (206124851420165607011/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree018.table
  base := (1319399922914625725088676240937654842833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-41745055649393125383810601430446452000000000000)
      constant := (194743006680559590178937632995945435927952696137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree018.table
  base := (1286359720814602988251589786348833109739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-41844766120846269206406112101140202000000000000)
      constant := (195558419604034643440661575449323043553657338771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20612485142016560701/10000000000000000000)
  centralHi := (206124851420165607011/100000000000000000000)
  directionLo := (26512590285951191249/12500000000000000000)
  directionHi := (212100722287609529993/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree019.table
  base := (218937251914671021006401515640561892247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-396552966215961438882564783902667318000000000000)
      constant := (1919401875622563656419264339799810070715173093847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree019.table
  base := (189429343635094340498197996773106522687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-44166690632751811688580237252695327000000000000)
      constant := (214196878916068703046978825520374184460361795143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26512590285951191249/12500000000000000000)
  centralHi := (212100722287609529993/100000000000000000000)
  directionLo := (43582555416985808759/20000000000000000000)
  directionHi := (54478194271232260949/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree020.table
  base := (-47299300484387303533661105262024379431/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-417400431587384749310834154931316568000000000000)
      constant := (2100003831586531893462895162257462828534540540304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree020.table
  base := (-783087381527595708237402776693135189427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-46488615144657354170754362404250452000000000000)
      constant := (234383029646318769403677591936906801772537344997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43582555416985808759/20000000000000000000)
  centralHi := (54478194271232260949/25000000000000000000)
  directionLo := (22357379193189502981/10000000000000000000)
  directionHi := (223573791931895029811/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree021.table
  base := (-405818116480273916499004976840954779713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-48694210773200895526567058439996202000000000000)
      constant := (254897980358952711515424183584782060357722726172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree021.table
  base := (-205832767125337547250213564820892671939/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-48810539656562896652928487555805577000000000000)
      constant := (256071259898298535676304220398421422374408203432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22357379193189502981/10000000000000000000)
  centralHi := (223573791931895029811/100000000000000000000)
  directionLo := (28636870481062795661/12500000000000000000)
  directionHi := (229094963848502365289/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree022.table
  base := (-2393506768836583812088368589396564536107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-459095362330231370167372896988615068000000000000)
      constant := (2501291108644459718267653757908053389079815654293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree022.table
  base := (-2414267534377383190954316018173463854759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-51132464168468439135102612707360702000000000000)
      constant := (279223325258486612543978747365875017617887394449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28636870481062795661/12500000000000000000)
  centralHi := (229094963848502365289/100000000000000000000)
  directionLo := (58621542799280986809/25000000000000000000)
  directionHi := (234486171197123947237/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree023.table
  base := (-615686623499788567783802225968399797973/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-479942827701654680595642268017264318000000000000)
      constant := (2721341381812733100593735577894303305859710938135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree023.table
  base := (-3096825312995722118361485384802531931631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-53454388680373981617276737858915827000000000000)
      constant := (303807027467261856524468795339929675065209896841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58621542799280986809/25000000000000000000)
  centralHi := (234486171197123947237/100000000000000000000)
  directionLo := (239756181368963321239/100000000000000000000)
  directionHi := (5993904534224083031/2500000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree024.table
  base := (-3687289194260620457460571679500492949229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-55643365897008665669323515449545952000000000000)
      constant := (328220837905315093737657884353423119241800426619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree024.table
  base := (-231472114276257314150403220705599300947/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-55776313192279524099450863010470952000000000000)
      constant := (329795189991992667758678097489639855399527355472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239756181368963321239/100000000000000000000)
  centralHi := (5993904534224083031/2500000000000000000)
  directionLo := (244912818216130838249/100000000000000000000)
  directionHi := (979651272864523353/400000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree025.table
  base := (-422788675006518628904419729395760116213/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-521637758444501301452181010074562818000000000000)
      constant := (3199022319016520652410785221839980228427835973870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree025.table
  base := (-848449163238585418192750554841920864941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-58098237704185066581624988162026077000000000000)
      constant := (357164839154746708126161862023832372420984761255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244912818216130838249/100000000000000000000)
  centralHi := (979651272864523353/400000000000000000)
  directionLo := (12498154918677782967/5000000000000000000)
  directionHi := (249963098373555659341/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree026.table
  base := (-4706838210218864684475769752084323619007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-542485223815924611880450381103212068000000000000)
      constant := (3456270269254010112148041715003509524197287451393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree026.table
  base := (-4719495141613485750500368092153198215571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-60420162216090609063799113313581202000000000000)
      constant := (385896535653767531009643411352492984525855506181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/5000000000000000000)
  centralHi := (249963098373555659341/100000000000000000000)
  directionLo := (25491334325697464059/10000000000000000000)
  directionHi := (254913343256974640591/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree027.table
  base := (-160304505588716022253522875082687140323/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-62592521020816435812079972459095702000000000000)
      constant := (413953643571753473376679889782550256937513832096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree027.table
  base := (-5140884490965262001109009099688038479243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-62742086727996151545973238465136327000000000000)
      constant := (415973821233032390579900779384542509952766983373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25491334325697464059/10000000000000000000)
  centralHi := (254913343256974640591/100000000000000000000)
  directionLo := (129884635920100739431/50000000000000000000)
  directionHi := (259769271840201478863/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree028.table
  base := (-2750675007785936764914138937419874277727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-584180154558771232736989123160510568000000000000)
      constant := (4006833980008658937191256065853792548688101553346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree028.table
  base := (-2755571059835212951629461235742952430567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-65064011239901694028147363616691452000000000000)
      constant := (447382756574741996925535245160094496223844327074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129884635920100739431/50000000000000000000)
  centralHi := (259769271840201478863/100000000000000000000)
  directionLo := (264536078095840847023/100000000000000000000)
  directionHi := (16533504880990052939/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree029.table
  base := (-728209667874215009134696471762162437769/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-605027619930194543165258494189159818000000000000)
      constant := (4299917127931137745273635166844427732172001912248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree029.table
  base := (-729284186600160918096441623878956920007/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-67385935751807236510321488768246577000000000000)
      constant := (480111533211376789061669232310629851806227867016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264536078095840847023/100000000000000000000)
  centralHi := (16533504880990052939/6250000000000000000)
  directionLo := (53843699217742876821/20000000000000000000)
  directionHi := (134609248044357192053/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree030.table
  base := (-3053067448306055424253629582663942821193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-69541676144624205954836429468645452000000000000)
      constant := (511637976956925705278271521064096488944423899646) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree030.table
  base := (-1222734444921650666872552372707373687767/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-69707860263712778992495613919801702000000000000)
      constant := (514150146466094898840384429406197579561023363685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53843699217742876821/20000000000000000000)
  centralHi := (134609248044357192053/50000000000000000000)
  directionLo := (273820855046158667657/100000000000000000000)
  directionHi := (136910427523079333829/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree031.table
  base := (-6345612170496542726533213429121178157837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-646722550673041164021797236246458318000000000000)
      constant := (4921231307681103103250814478402731545552564288563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree031.table
  base := (-1270442754622999453634464169711215977943/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-72029784775618321474669739071356827000000000000)
      constant := (549490119232726772982928709745284307619009995365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273820855046158667657/100000000000000000000)
  centralHi := (136910427523079333829/50000000000000000000)
  directionLo := (278347126229371642933/100000000000000000000)
  directionHi := (139173563114685821467/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree032.table
  base := (-1636639659284909736765513438203003949207/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-667570016044464474450066607275107568000000000000)
      constant := (5249320681771251266120329947841680170453906244772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree032.table
  base := (-1638083668679818936368719518837811418949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-74351709287523863956843864222911952000000000000)
      constant := (586124268385120085634303016237362285486888246156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278347126229371642933/100000000000000000000)
  centralHi := (139173563114685821467/50000000000000000000)
  directionLo := (282800963050146039989/100000000000000000000)
  directionHi := (28280096305014603999/10000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree033.table
  base := (-3355525410065786684357259407799483877891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-76490831268431976097592886478195202000000000000)
      constant := (620994979877287327507422656005059533247824399402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree033.table
  base := (-3358049802254602112848697143921109135907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-76673633799429406439017989374467077000000000000)
      constant := (624046507077358989577840779609849579202266136554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282800963050146039989/100000000000000000000)
  centralHi := (28280096305014603999/10000000000000000000)
  directionLo := (57437147117185540227/20000000000000000000)
  directionHi := (17949108474120481321/6250000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree034.table
  base := (-1068882673668539829093964257408770049/1562500000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (11567934)
      previous := (5783967)
      next := (5783967)
      square := (71087700824241360579858195812250000000000000)
      linear := (-2454203968122183720784101554783412000000000000)
      constant := (20553934293852324437410691036664430675656697600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree034.table
  base := (-6845258160857724191559718785374747694201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7898633424915706731095355090250000000000000)
      linear := (-273341032219152072391668216353018000000000000)
      constant := (2294988502898705183843224643812066698771455599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57437147117185540227/20000000000000000000)
  centralHi := (17949108474120481321/6250000000000000000)
  directionLo := (14575228021026866161/5000000000000000000)
  directionHi := (291504560420537323221/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree035.table
  base := (-1387489183352295040504328865333542009769/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-730112412158734405734874720361055318000000000000)
      constant := (6302677660154177583129030971324857598648295335155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree035.table
  base := (-694129296333870136284795938263485441439/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-81317482823240491403366239677577327000000000000)
      constant := (703735408271763613076877936791585480309335399290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14575228021026866161/5000000000000000000)
  centralHi := (291504560420537323221/100000000000000000000)
  directionLo := (295760326561746630539/100000000000000000000)
  directionHi := (14788016328087331527/5000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree036.table
  base := (-7002106459639088355300702315693445792629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-83439986392239746240349343487744952000000000000)
      constant := (741854799628954137277588814078541697086654164019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree036.table
  base := (-700546040030447728738174621591257048367/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-83639407335146033885540364829132452000000000000)
      constant := (745493995934791168175028798210679047995367793370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295760326561746630539/100000000000000000000)
  centralHi := (14788016328087331527/5000000000000000000)
  directionLo := (37494464756033348901/12500000000000000000)
  directionHi := (299955718048266791209/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree037.table
  base := (-879487921123707900498789449155509282751/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-771807342901581026591413462418353818000000000000)
      constant := (7062105160593979412457920003184985511676919875592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree037.table
  base := (-7038825153273464189285019391698650291937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-85961331847051576367714489980687577000000000000)
      constant := (788524301550935529049739183854363757384493741607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37494464756033348901/12500000000000000000)
  centralHi := (299955718048266791209/100000000000000000000)
  directionLo := (4751456777324725703/1562500000000000000)
  directionHi := (304093233748782444993/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree038.table
  base := (-7039745998128731237841434125713254917053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-792654808273004337019682833447003068000000000000)
      constant := (7458889424263794426794363906239908658223561244547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree038.table
  base := (-880286181320440183274563704531323194609/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-88283256358957118849888615132242702000000000000)
      constant := (832823665270817325907283725694597885976226782392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4751456777324725703/1562500000000000000)
  centralHi := (304093233748782444993/100000000000000000000)
  directionLo := (308175204767891657743/100000000000000000000)
  directionHi := (19260950297993228609/6250000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree039.table
  base := (-7014405279543372060928672023057490996771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-90389141516047516383105800497294702000000000000)
      constant := (874113948074640906700173390060041854924820379381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree039.table
  base := (-7016617855874132417507048197910932920669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-90605180870862661332062740283797827000000000000)
      constant := (878389833092604312727044607427286474301837848459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308175204767891657743/100000000000000000000)
  centralHi := (19260950297993228609/6250000000000000000)
  directionLo := (19512738112703962483/6250000000000000000)
  directionHi := (312203809803263399729/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree040.table
  base := (-6960534795518211696687733175464258179463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-834349739015850957876221575504301568000000000000)
      constant := (8286496144449205505340268948473119475111685934137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree040.table
  base := (-870307284232394981553799186047103083941/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-92927105382768203814236865435352952000000000000)
      constant := (925220894935713387753669649230247735330939690008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19512738112703962483/6250000000000000000)
  centralHi := (312203809803263399729/100000000000000000000)
  directionLo := (31618108874126640633/10000000000000000000)
  directionHi := (316181088741266406331/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree041.table
  base := (-3439344320534707639137398234066439917747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-855197204387274268304490946532950818000000000000)
      constant := (8717286557903307460649317823756741508267924961306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree041.table
  base := (-688035975029158227570786726138576064529/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-95249029894673746296410990586908077000000000000)
      constant := (973315232164340736560094512595827436909987649190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31618108874126640633/10000000000000000000)
  centralHi := (316181088741266406331/100000000000000000000)
  directionLo := (160054477365952572099/50000000000000000000)
  directionHi := (320108954731905144199/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree042.table
  base := (-846167070957403177802956548871323327361/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-97338296639855286525862257506844452000000000000)
      constant := (1017709367690222987096132244816315748265309094968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree042.table
  base := (-1354157511219743542232747274553612895627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-97570954406579288778585115738463202000000000000)
      constant := (1022671473118383513080781138473287616060719465985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160054477365952572099/50000000000000000000)
  centralHi := (320108954731905144199/100000000000000000000)
  directionLo := (323989204945925955097/100000000000000000000)
  directionHi := (161994602472962977549/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree043.table
  base := (-3316438410852746637692755627412186857529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-896892135130120889161029688590249318000000000000)
      constant := (9612778831782349967676780828056568688768735382542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree043.table
  base := (-3317067984896842264776521327714619888739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-99892878918484831260759240890018327000000000000)
      constant := (1073288455429694256691208666340499719558654660458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323989204945925955097/100000000000000000000)
  centralHi := (161994602472962977549/50000000000000000000)
  directionLo := (327823530185728928437/100000000000000000000)
  directionHi := (163911765092864464219/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree044.table
  base := (-258785881153096857546221471619981842527/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-917739600501544199589299059618898568000000000000)
      constant := (10077461167460969907679936216154047645715444296825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree044.table
  base := (-258829564381207630098855709324370912363/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-102214803430390373742933366041573452000000000000)
      constant := (1125165194088219320463699325861688755033566892325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327823530185728928437/100000000000000000000)
  centralHi := (163911765092864464219/50000000000000000000)
  directionLo := (331613523495912091063/100000000000000000000)
  directionHi := (41451690436989011383/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree045.table
  base := (-3139966710661316155175829766741675621249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-104287451763663056668618714516394202000000000000)
      constant := (1172602635744808235112472282467708003018855313678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree045.table
  base := (-1256176022478407281262366069673557273711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-104536727942295916225107491193128577000000000000)
      constant := (1178300854380636461462244075102895866677513058605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331613523495912091063/100000000000000000000)
  centralHi := (41451690436989011383/12500000000000000000)
  directionLo := (83840171974460636179/25000000000000000000)
  directionHi := (335360687897842544717/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree046.table
  base := (-6063978661073474844636033683889377888663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-959434531244390820445837801676197068000000000000)
      constant := (11040660056009827942460381247099613808466304464937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree046.table
  base := (-6064798913106424649412841911641632963107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-106858652454201458707281616344683702000000000000)
      constant := (1232694728958015694054979964000862684419426847477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83840171974460636179/25000000000000000000)
  centralHi := (335360687897842544717/100000000000000000000)
  directionLo := (169533221677385749483/50000000000000000000)
  directionHi := (339066443354771498967/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree047.table
  base := (-5821988471685177348230163870050741321431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-980281996615814130874107172704846318000000000000)
      constant := (11539164711957152861802519686100631479115994241769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree047.table
  base := (-116453976717698373900044314131273976893/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-109180576966107001189455741496238827000000000000)
      constant := (1288346218402485475060185495422282216261774626150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169533221677385749483/50000000000000000000)
  centralHi := (339066443354771498967/100000000000000000000)
  directionLo := (342732133059033121273/100000000000000000000)
  directionHi := (171366066529516560637/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree048.table
  base := (-2777068630555527332309375979490461821729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-111236606887470826811375171525943952000000000000)
      constant := (1338770340223747861556237790892291983796881548238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree048.table
  base := (-5554752180485994891372647043470196905167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-111502501478012543671629866647793952000000000000)
      constant := (1345254814759023137698698805542400686676043124137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342732133059033121273/100000000000000000000)
  centralHi := (171366066529516560637/50000000000000000000)
  directionLo := (346359029120268638483/100000000000000000000)
  directionHi := (86589757280067159621/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree049.table
  base := (-1052114577685717394588814500312755068671/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1021976927358660751730645914762144818000000000000)
      constant := (12569961183064082793896616221543637354506055112645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree049.table
  base := (-5261104955960519800178087398846628269623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-113824425989918086153803991799349077000000000000)
      constant := (1403420087579951921819640058206857431136235399553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346359029120268638483/100000000000000000000)
  centralHi := (86589757280067159621/25000000000000000000)
  directionLo := (87487084430744480769/25000000000000000000)
  directionHi := (349948337722977923077/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree050.table
  base := (-4941420705039523164060472533899076432863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1042824392730084062158915285790794068000000000000)
      constant := (13102245749184411307100938886745884700923056160737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree050.table
  base := (-4941880892125850840675032963249297441009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-116146350501823628635978116950904202000000000000)
      constant := (1462841672098758304006230788817731504456433218199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87487084430744480769/25000000000000000000)
  centralHi := (349948337722977923077/100000000000000000000)
  directionLo := (353501203812682549987/100000000000000000000)
  directionHi := (88375300953170637497/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree051.table
  base := (-919357396147469990514120587205692823837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7898633424915706731095355090250000000000000)
      linear := (-408947273395427671121562728496518000000000000)
      constant := (5246360607742957862177782462039504137520193815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree051.table
  base := (-2298592419485885925402574500242377868901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7898633424915706731095355090250000000000000)
      linear := (-409924827037125159578381460562143000000000000)
      constant := (5271692938437165233264558447643988631718681798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353501203812682549987/100000000000000000000)
  centralHi := (88375300953170637497/25000000000000000000)
  directionLo := (3570187153623126833/1000000000000000000)
  directionHi := (357018715362312683301/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree052.table
  base := (-4226761808274259999434893400997750083289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1084519323472930683015454027848092568000000000000)
      constant := (14200573367316083600980112562680158431592359537511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree052.table
  base := (-2113552823693361981856946896267915947077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-120790199525634713600326367254014452000000000000)
      constant := (1585452586968372413509546204899928585886995428294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3570187153623126833/1000000000000000000)
  centralHi := (357018715362312683301/100000000000000000000)
  directionLo := (72100381452776338811/20000000000000000000)
  directionHi := (45062738407985211757/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree053.table
  base := (-76628431316151096683704114836395642003/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1105366788844353993443723398876741818000000000000)
      constant := (14766612002387913483287975510847940110173357979850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree053.table
  base := (-3831718610343701578340165863281931811887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-123112124037540256082500492405569577000000000000)
      constant := (1648641433408467825209923850999814004551625866057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72100381452776338811/20000000000000000000)
  centralHi := (45062738407985211757/12500000000000000000)
  directionLo := (363951764884904317569/100000000000000000000)
  directionHi := (36395176488490431757/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree054.table
  base := (-136433240180906173705892030287995107659/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-125134917135086367096888085545043452000000000000)
      constant := (1704877569769400642946215932924716227776417158725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree054.table
  base := (-1705543765805117301044178786806722855123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-125434048549445798564674617557124702000000000000)
      constant := (1713085610429441774037400421997943980949526580106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363951764884904317569/100000000000000000000)
  centralHi := (36395176488490431757/10000000000000000000)
  directionLo := (183684613662098128687/50000000000000000000)
  directionHi := (2938953818593570059/800000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree055.table
  base := (-370630627310788338790971818913819488003/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1147061719587200614300262140934040318000000000000)
      constant := (15932430287432811400340858620484291533499156108776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree055.table
  base := (-2965266478814318662946563514651833371217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-127755973061351341046848742708679827000000000000)
      constant := (1778784958635114909989056124099273841833482245687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183684613662098128687/50000000000000000000)
  centralHi := (2938953818593570059/800000000000000000)
  directionLo := (370755190397541569733/100000000000000000000)
  directionHi := (185377595198770784867/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree056.table
  base := (-2494110145099237353803581941610340642121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1167909184958623924728531511962689568000000000000)
      constant := (16532207246144937820029042739975858220200391289079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree056.table
  base := (-311787658628358019768485257497066102249/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-130077897573256883529022867860234952000000000000)
      constant := (1845739342952684469902822429552736167133494782712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370755190397541569733/100000000000000000000)
  centralHi := (185377595198770784867/50000000000000000000)
  directionLo := (18705525469006318131/5000000000000000000)
  directionHi := (374110509380126362621/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree057.table
  base := (-999032918577500480331354443855167889753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-132084072258894137239644542554593202000000000000)
      constant := (1904803106363096084996900728148887850402131935966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree057.table
  base := (-499557681918248049942865848646777518851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-132399822085162426011196993011790077000000000000)
      constant := (1913948648921341733904511028568585735869912297044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18705525469006318131/5000000000000000000)
  centralHi := (374110509380126362621/100000000000000000000)
  directionLo := (47179500191191011087/12500000000000000000)
  directionHi := (377436001529528088697/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree058.table
  base := (-9230909632937476019142958613294733159/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1209604115701470545585070254019988068000000000000)
      constant := (17765491533369175206926337128573257176519064262560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree058.table
  base := (-369271938839360183157916238954925443239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-134721746597067968493371118163345202000000000000)
      constant := (1983412779547175780711132106943743729719867918916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47179500191191011087/12500000000000000000)
  centralHi := (377436001529528088697/100000000000000000000)
  directionLo := (380732448410347925083/100000000000000000000)
  directionHi := (95183112102586981271/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree059.table
  base := (-37231104486315414293745420671324046361/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1230451581072893856013339625048637318000000000000)
      constant := (18398997222118894129548473789010748191284720320975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree059.table
  base := (-930900231912389824397281800088658590273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-137043671108973510975545243314900327000000000000)
      constant := (2054131652637960038419172034329140610210260661703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380732448410347925083/100000000000000000000)
  centralHi := (95183112102586981271/25000000000000000000)
  directionLo := (384000598039219932179/100000000000000000000)
  directionHi := (19200029901960996609/5000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree060.table
  base := (-359586087735416281463176320865400724411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-139033227382701907382400999564142952000000000000)
      constant := (2115971598413751112282230219044606361643771899421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree060.table
  base := (-44961472813025706811903835472504154359/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-139365595620879053457719368466455452000000000000)
      constant := (2126105198544601419725090291131358975600639440392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (384000598039219932179/100000000000000000000)
  centralHi := (19200029901960996609/5000000000000000000)
  directionLo := (387241166866874929081/100000000000000000000)
  directionHi := (193620583433437464541/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree061.table
  base := (47321730751347273213390784703612741111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1272146511815740476869878367105935818000000000000)
      constant := (19699732483491968298019789715802590914704813409555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree061.table
  base := (236517573153908841507658605952167950907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-141687520132784595939893493618010577000000000000)
      constant := (2199333358247203647899774597690017758487221466723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387241166866874929081/100000000000000000000)
  centralHi := (193620583433437464541/50000000000000000000)
  directionLo := (390454841612137251693/100000000000000000000)
  directionHi := (195227420806068625847/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree062.table
  base := (42889466832947162220552865850094317273/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1292993977187163787298147738134585068000000000000)
      constant := (20366961057051879902953472276154168833028707433460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree062.table
  base := (171542174129537102754938197602004283301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-144009444644690138422067618769565702000000000000)
      constant := (2273816081733163627567641041440178062527762808945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390454841612137251693/100000000000000000000)
  centralHi := (195227420806068625847/50000000000000000000)
  directionLo := (393642280961153234819/100000000000000000000)
  directionHi := (19682114048057661741/5000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree063.table
  base := (1503941315597886993455452247849133597701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-145982382506509677525157456573692702000000000000)
      constant := (2338381079757857669457264222319401742918912743389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree063.table
  base := (1503873734651654930336151451952477324757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-146331369156595680904241743921120827000000000000)
      constant := (2349553326622742470876463457226423743548865539373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393642280961153234819/100000000000000000000)
  centralHi := (19682114048057661741/5000000000000000000)
  directionLo := (79360823428752254107/20000000000000000000)
  directionHi := (49600514642970158817/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree064.table
  base := (13594076094275944892111918689619690457/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1334688907930010408154686480191883568000000000000)
      constant := (21735138136380775660749922157569498754012348809120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree064.table
  base := (1087496991927448956907831888601963659491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-148653293668501223386415869072675952000000000000)
      constant := (2426545057004351451419529501453014276885890325398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79360823428752254107/20000000000000000000)
  centralHi := (49600514642970158817/12500000000000000000)
  directionLo := (12498154918677782967/3125000000000000000)
  directionHi := (79988191479537810989/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree065.table
  base := (2871111390058944268738142731754308161269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1355536373301433718582955851220532818000000000000)
      constant := (22436086033472759380532398349036464921835626284469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree065.table
  base := (2871061296168741129015827146084139571271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-150975218180406765868589994224231077000000000000)
      constant := (2504791242447554494312750403940755565569528751119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/3125000000000000000)
  centralHi := (79988191479537810989/20000000000000000000)
  directionLo := (403053385330182341789/100000000000000000000)
  directionHi := (40305338533018234179/10000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree066.table
  base := (3592110038112488140855184564325132182521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-152931537630317447667913913583242452000000000000)
      constant := (2572030352484460789044452768626852596610836152369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree066.table
  base := (359206692501853705878938730499774654107/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-153297142692312308350764119375786202000000000000)
      constant := (2584291857166671093531947033044419896102516515230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403053385330182341789/100000000000000000000)
  centralHi := (40305338533018234179/10000000000000000000)
  directionLo := (40614196218571254733/10000000000000000000)
  directionHi := (406141962185712547331/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree067.table
  base := (2169020277754386047394630804658713987767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1397231304044280339439494593277831318000000000000)
      constant := (23871699352355836434801896198314074580806676490734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree067.table
  base := (1084500864731267596447075292054627369887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-155619067204217850832938244527341327000000000000)
      constant := (2665046879312000900671414113771451687018051183772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40614196218571254733/10000000000000000000)
  centralHi := (406141962185712547331/100000000000000000000)
  directionLo := (409207228027561941393/100000000000000000000)
  directionHi := (204603614013780970697/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree068.table
  base := (2554448265174295880251701578615810173267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (11567934)
      previous := (5783967)
      next := (5783967)
      square := (71087700824241360579858195812250000000000000)
      linear := (-4906846952995514359404027558153912000000000000)
      constant := (85143129423301666986606715863583693832394940006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree068.table
  base := (2554432308885202945336189676385910068377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7898633424915706731095355090250000000000000)
      linear := (-546508621855098246765094704771268000000000000)
      constant := (9505385087782689661620422998422099337215027554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409207228027561941393/100000000000000000000)
  centralHi := (204603614013780970697/50000000000000000000)
  directionLo := (412249702840331214021/100000000000000000000)
  directionHi := (206124851420165607011/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree069.table
  base := (5904672527217777334298224671942828853107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-159880692754125217810670370592792202000000000000)
      constant := (2816918686786491172711182682523003712870727362523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree069.table
  base := (5904645080150808711699471296427139805051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-160262916228028935797286494830451577000000000000)
      constant := (2830320074650288512837792876453169293785732997539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412249702840331214021/100000000000000000000)
  centralHi := (206124851420165607011/50000000000000000000)
  directionLo := (41526988755974313287/10000000000000000000)
  directionHi := (415269887559743132871/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree070.table
  base := (6725363938528004910890788746716190791867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1459773700158550270724302706363779068000000000000)
      constant := (26109410563336328732513390945799760103758639529467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree070.table
  base := (6725340337073412534843059438874777093527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-162584840739934478279460619982006702000000000000)
      constant := (2914838218862362232301033881371143605226878919903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41526988755974313287/10000000000000000000)
  centralHi := (415269887559743132871/100000000000000000000)
  directionLo := (104567066258879407197/25000000000000000000)
  directionHi := (418268265035517628789/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree071.table
  base := (7570966858487095109137446940328524777127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1480621165529973581152572077392428318000000000000)
      constant := (26877791446476299650591393717348932713035080042727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree071.table
  base := (7570946567977047042016070740801612877789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-164906765251840020761634745133561827000000000000)
      constant := (3000610711742064110556146260228514068732268095221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104567066258879407197/25000000000000000000)
  centralHi := (418268265035517628789/100000000000000000000)
  directionLo := (210622650466279583789/50000000000000000000)
  directionHi := (421245300932559167579/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree072.table
  base := (8441477976254171365312790791183866947357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-166829847877932987953426827602341952000000000000)
      constant := (3073045638072494576455973597333256599124966750773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree072.table
  base := (8441460535670945007814474939664018452533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-167228689763745563243808870285116952000000000000)
      constant := (3087637543745867655844355870852608700495709559437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210622650466279583789/50000000000000000000)
  centralHi := (421245300932559167579/100000000000000000000)
  directionLo := (26512590285951191249/6250000000000000000)
  directionHi := (84840288915043811997/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree073.table
  base := (9336894485359378410332086852945292088643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1522316096272820202009110819449726818000000000000)
      constant := (28448268377401277162697070237081188325374839079043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree073.table
  base := (9336879497304780488661782735244716864573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-169550614275651105725982995436672077000000000000)
      constant := (3175918706787605993604990244478839248721562150997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26512590285951191249/6250000000000000000)
  centralHi := (84840288915043811997/20000000000000000000)
  directionLo := (53392141217370850923/12500000000000000000)
  directionHi := (85427425947793361477/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree074.table
  base := (10257214006912378993002681694309759889923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1543163561644243512437380190478376068000000000000)
      constant := (29250364287604153655262535614439838773517108864323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree074.table
  base := (5128600564461960274582736115706703590963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-171872538787556648208157120588227202000000000000)
      constant := (3265454194016054033982180976622964830665557039414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53392141217370850923/12500000000000000000)
  centralHi := (85427425947793361477/20000000000000000000)
  directionLo := (430052775393419914581/100000000000000000000)
  directionHi := (215026387696709957291/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree075.table
  base := (560121726225035108333635200239372565039/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-173779003001740758096183284611891702000000000000)
      constant := (3340410935528889982250484754479602795017865209420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree075.table
  base := (11202423461537003380257584974032049557153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-174194463299462190690331245739782327000000000000)
      constant := (3356243999626450002131594718713884086571897630617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430052775393419914581/100000000000000000000)
  centralHi := (215026387696709957291/50000000000000000000)
  directionLo := (54118598300041974763/12500000000000000000)
  directionHi := (86589757280067159621/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree076.table
  base := (6086277164499254295126460664808726847227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1584858492387090133293918932535674568000000000000)
      constant := (30888270728520949938477460036746034673001662785654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree076.table
  base := (6086272413469619418253232537315887078597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-176516387811367733172505370891337452000000000000)
      constant := (3448288118700777706478176005775016714443307902266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54118598300041974763/12500000000000000000)
  centralHi := (86589757280067159621/20000000000000000000)
  directionLo := (43582555416985808759/10000000000000000000)
  directionHi := (435825554169858087591/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree077.table
  base := (6583785985888599400294906956951264734961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1605705957758513443722188303564323818000000000000)
      constant := (31724081175450799597467268181622410146322075911522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree077.table
  base := (6583781905901426138305062026935552627207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-178838312323273275654679496042892577000000000000)
      constant := (3541586547072421081207423499892289382443380114846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43582555416985808759/10000000000000000000)
  centralHi := (435825554169858087591/100000000000000000000)
  directionLo := (219341728639014457843/50000000000000000000)
  directionHi := (438683457278028915687/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree078.table
  base := (3546871556259730432930001117095497885477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-180728158125548528238939741621441452000000000000)
      constant := (3619014414219182529629215895782408703062792013812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree078.table
  base := (709373960938661115783875357198916305373/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-181160236835178818136853621194447702000000000000)
      constant := (3636139281211472137915375116306436737935815643940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219341728639014457843/50000000000000000000)
  centralHi := (438683457278028915687/100000000000000000000)
  directionLo := (27595178878020334213/6250000000000000000)
  directionHi := (441522862048325347409/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree079.table
  base := (7616148024094359286766923501223350695709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1647400888501360064578727045621622318000000000000)
      constant := (33429416358476580482352648652754559075624916901818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree079.table
  base := (304645800670034748306884455432569657597/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-183482161347084360619027746346002827000000000000)
      constant := (3731946318127540892760505714228446791089774106650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27595178878020334213/6250000000000000000)
  centralHi := (441522862048325347409/100000000000000000000)
  directionLo := (444344123099748951713/100000000000000000000)
  directionHi := (222172061549874475857/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree080.table
  base := (3260400111865216363303760848603140997871/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1668248353872783375006996416650271568000000000000)
      constant := (34298941043563322076987483195289312780357263333355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree080.table
  base := (16301995396709502828114812149033437391081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-185804085858989903101201871497557952000000000000)
      constant := (3829007655287396688205566154056087997404834594209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444344123099748951713/100000000000000000000)
  centralHi := (222172061549874475857/50000000000000000000)
  directionLo := (447147583863790059621/100000000000000000000)
  directionHi := (223573791931895029811/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree081.table
  base := (17396599011076631613528162734209521210617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-187677313249356298381696198630991202000000000000)
      constant := (3908855973711436873064965835968562987676286660913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree081.table
  base := (17396594580514249171419094300583782487139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-188126010370895445583375996649113077000000000000)
      constant := (3927323290545177812588764493527156995353727127371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447147583863790059621/100000000000000000000)
  centralHi := (223573791931895029811/50000000000000000000)
  directionLo := (112483394268100046703/25000000000000000000)
  directionHi := (449933577072400186813/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree082.table
  base := (18516090770103235420692717380693173765247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1709943284615629995863535158707570068000000000000)
      constant := (36071704501191201720447171249215112447571719366847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree082.table
  base := (9258043484184962021757655530823457009607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-190447934882800988065550121800668202000000000000)
      constant := (4026893222083251630831102274555840215603990582046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112483394268100046703/25000000000000000000)
  centralHi := (449933577072400186813/100000000000000000000)
  directionLo := (45270242521893539511/10000000000000000000)
  directionHi := (452702425218935395111/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree083.table
  base := (9830237649868232102235793794970639771331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1730790749987053306291804529736219318000000000000)
      constant := (36974943242688788502244356861657211378290821856262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree083.table
  base := (9830236019033853222344695498445729305919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-192769859394706530547724246952223327000000000000)
      constant := (4127717448362100062040353439998423024952514877582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45270242521893539511/10000000000000000000)
  centralHi := (452702425218935395111/100000000000000000000)
  directionLo := (22772722049693911601/5000000000000000000)
  directionHi := (455454440993878232021/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree084.table
  base := (10414876072624768898157007968421767465563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-194626468373164068524452655640540952000000000000)
      constant := (4209935552870057448377038406209293288051568318214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree084.table
  base := (10414874673665648598927222088485059315469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-195091783906612073029898372103778452000000000000)
      constant := (4229795968077853213651839077609985878064563377482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22772722049693911601/5000000000000000000)
  centralHi := (455454440993878232021/100000000000000000000)
  directionLo := (458189927697004730577/100000000000000000000)
  directionHi := (229094963848502365289/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree085.table
  base := (4404784184275038671708035865988430615519/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (11567934)
      previous := (5783967)
      next := (5783967)
      square := (71087700824241360579858195812250000000000000)
      linear := (-6133168445432179678713990559839162000000000000)
      constant := (134308424534235874405561534893057241631900919355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree085.table
  base := (22023918521610617876372610366615885596329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7898633424915706731095355090250000000000000)
      linear := (-683092416673071333951807948980393000000000000)
      constant := (14993525190748457160923359185631144273968152129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458189927697004730577/100000000000000000000)
  centralHi := (229094963848502365289/50000000000000000000)
  directionLo := (230454589813767181393/50000000000000000000)
  directionHi := (460909179627534362787/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree086.table
  base := (23242981301723189834958974828843957962563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1793333146101323237576612642822167068000000000000)
      constant := (39752087377719693191400222293998954094673049528963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree086.table
  base := (23242979243738454168199178822647184830823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-199735632930423157994246622406888702000000000000)
      constant := (4437715883572415603931407041860512050980716147247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230454589813767181393/50000000000000000000)
  centralHi := (460909179627534362787/100000000000000000000)
  directionLo := (115903120613420891361/25000000000000000000)
  directionHi := (92722496490736713089/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree087.table
  base := (382608328278267381977094970352176391413/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-201575623496971838667209112650090702000000000000)
      constant := (4522253114496798615893170224483748436617399024448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree087.table
  base := (3060866405645720821924009970651158359169/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-202057557442328700476420747558443827000000000000)
      constant := (4543557277624481197621059250694097736992393424328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115903120613420891361/25000000000000000000)
  centralHi := (92722496490736713089/20000000000000000000)
  directionLo := (93260022712587276401/20000000000000000000)
  directionHi := (233150056781468191003/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree088.table
  base := (25755775811449184583596028327237393865733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1835028076844169858433151384879465568000000000000)
      constant := (41659706642435099215909398283342952235198114408133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree088.table
  base := (25755774298534768112154682130581481946827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-204379481954234242958594872709998952000000000000)
      constant := (4650652961612229909698637226872144606531139263603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93260022712587276401/20000000000000000000)
  centralHi := (233150056781468191003/50000000000000000000)
  directionLo := (468972342394247894473/100000000000000000000)
  directionHi := (234486171197123947237/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree089.table
  base := (27049509508313133550267284676947885707639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1855875542215593168861420755908114818000000000000)
      constant := (42630373208349170552297368771861224453351529766839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree089.table
  base := (422648565802900420389667297627963365521/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-206701406466139785440768997861554077000000000000)
      constant := (4759002934968273026875883898487380511603908119616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468972342394247894473/100000000000000000000)
  centralHi := (234486171197123947237/50000000000000000000)
  directionLo := (117907357688326642101/25000000000000000000)
  directionHi := (94325886150661313681/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree090.table
  base := (14184066966229406009984732854593952863547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-208524778620779608809965569659640452000000000000)
      constant := (4845808635973047330852628586688117993807082823366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree090.table
  base := (28368132820823801171039955041718321614699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-209023330978045327922943123013109202000000000000)
      constant := (4868607197212382942363168624809874067550756360211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117907357688326642101/25000000000000000000)
  centralHi := (94325886150661313681/20000000000000000000)
  directionLo := (94854326622379921899/20000000000000000000)
  directionHi := (59283954138987451187/12500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree091.table
  base := (29711648941699113915728794018547171077503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1897570472958439789717959497965413318000000000000)
      constant := (44605420184887243301732027890222417349812342675903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree091.table
  base := (14855823994500705365411334534313825651951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-211345255489950870405117248164664327000000000000)
      constant := (4979465747938171836929589206495841071529869143278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94854326622379921899/20000000000000000000)
  centralHi := (59283954138987451187/12500000000000000000)
  directionLo := (476899196892350223031/100000000000000000000)
  directionHi := (59612399611543777879/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree092.table
  base := (3108005441567447519865251999196236960039/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1918417938329863100146228868994062568000000000000)
      constant := (45609800588545146163381783016123054808095597392390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree092.table
  base := (15540026799644209096577071490941384951929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-213667180001856412887291373316219452000000000000)
      constant := (5091578586801803980272758615012975627243094827362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476899196892350223031/100000000000000000000)
  centralHi := (59612399611543777879/12500000000000000000)
  directionLo := (479512362737926642479/100000000000000000000)
  directionHi := (5993904534224083031/1250000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree093.table
  base := (32473350252523538551184079988882098350637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-215473933744587378952722026669190202000000000000)
      constant := (5180602103558718604369588949841820934944431082693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree093.table
  base := (16236674776514174396574415066210449946597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-215989104513761955369465498467774577000000000000)
      constant := (5204945713512431304359540184026188899970226406266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479512362737926642479/100000000000000000000)
  centralHi := (5993904534224083031/1250000000000000000)
  directionLo := (120527841192514845269/25000000000000000000)
  directionHi := (482111364770059381077/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree094.table
  base := (8472884091515228336710150198188763800791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1960112869072709721002767611051361068000000000000)
      constant := (47652275213050467310965845082619432563449564982364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree094.table
  base := (6778307153357868267509488964412916712587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-218311029025667497851639623619329702000000000000)
      constant := (5319567127824089256956559339220826606591469481215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120527841192514845269/25000000000000000000)
  centralHi := (482111364770059381077/100000000000000000000)
  directionLo := (484696430833144848621/100000000000000000000)
  directionHi := (242348215416572424311/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree095.table
  base := (35334612683384825530089406227917294722483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-1980960334444133031431036982080010318000000000000)
      constant := (48690369429676857514738005172285854747829991664883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree095.table
  base := (1413384486801397405875817462086880059957/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-220632953537573040333813748770884827000000000000)
      constant := (5435442829528830074235783594271898284351964304325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484696430833144848621/100000000000000000000)
  centralHi := (242348215416572424311/50000000000000000000)
  directionLo := (9745355654553196097/2000000000000000000)
  directionHi := (487267782727659804851/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree096.table
  base := (18401289571424602492379823915751167266683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-222423088868395149095478483678739952000000000000)
      constant := (5526633508919110571090930312589918077912136437574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree096.table
  base := (36802578703150533259337681184564068393761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-222954878049478582815987873922439952000000000000)
      constant := (5552572818450904618654534438114003691826894472729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9745355654553196097/2000000000000000000)
  centralHi := (487267782727659804851/100000000000000000000)
  directionLo := (244912818216130838249/50000000000000000000)
  directionHi := (489825636432261676499/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree097.table
  base := (38295435692344721868814723141920683988699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2022655265186979652287575724137308818000000000000)
      constant := (50800271663453273707264829397860192324556036815899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree097.table
  base := (38295435315771257399976591768638243450137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-225276802561384125298161999073995077000000000000)
      constant := (5670957094441832746584247318531527935119670938193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244912818216130838249/50000000000000000000)
  centralHi := (489825636432261676499/100000000000000000000)
  directionLo := (98474040463100834819/20000000000000000000)
  directionHi := (30773137644719010881/6250000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree098.table
  base := (9953295571960432641041021085617987412579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2043502730558402962715845095165958068000000000000)
      constant := (51872079678052463391792056420737147602153854015116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree098.table
  base := (4976647745670649236003419750256342792271/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-227598727073289667780336124225550202000000000000)
      constant := (5790595657376226591153651024905044629428987360952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98474040463100834819/20000000000000000000)
  centralHi := (30773137644719010881/6250000000000000000)
  directionLo := (494901685337755569981/100000000000000000000)
  directionHi := (247450842668877784991/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree099.table
  base := (20677909446077620603309849234418639553173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-229372243992202919238234940688289702000000000000)
      constant := (5883902847009215806349615086301824035823348472794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree099.table
  base := (41355818616033049339257894165124481279347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-229920651585195210262510249377105327000000000000)
      constant := (5911488507148251840428918171877316680515348817883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494901685337755569981/100000000000000000000)
  centralHi := (247450842668877784991/50000000000000000000)
  directionLo := (99484057048773627319/20000000000000000000)
  directionHi := (124355071310967034149/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree100.table
  base := (42923345473898109954387623687081491007773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2085197661301249583572383837223256568000000000000)
      constant := (54049409497711921461815573324112621271692530462173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree100.table
  base := (21461672618745591792871427894242358353961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-232242576097100752744684374528660452000000000000)
      constant := (6033635643668629627951029898596969569994741061058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99484057048773627319/20000000000000000000)
  centralHi := (124355071310967034149/25000000000000000000)
  directionLo := (12498154918677782967/2500000000000000000)
  directionHi := (499926196747111318681/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree101.table
  base := (8903152401318757232266834290317309703457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (327726)
      previous := (163863)
      next := (163863)
      square := (2013954076875380179156849190250000000000000)
      linear := (-206454771754991951181320773282218000000000000)
      constant := (5406816125991265950038121996407107112693458285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree101.table
  base := (44515761804210028114017537109423115732357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (36414)
      previous := (18207)
      next := (18207)
      square := (223772675208375575461872132250000000000000)
      linear := (-22994265327811616040276296410177000000000000)
      constant := (603571911269688904382971723764015905446651173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/2500000000000000000)
  centralHi := (499926196747111318681/100000000000000000000)
  directionLo := (502419609704847975679/100000000000000000000)
  directionHi := (392515320081912481/78125000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree102.table
  base := (23066534233962159061425622118930034009469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7898633424915706731095355090250000000000000)
      linear := (-817721104207649444224883729058268000000000000)
      constant := (21634637075380904255828714273671396553861186538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree102.table
  base := (2306653414734208500719820831034053097499/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7898633424915706731095355090250000000000000)
      linear := (-819676211491044421138521193189518000000000000)
      constant := (21735961164931669986741904010455966012951745980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502419609704847975679/100000000000000000000)
  centralHi := (392515320081912481/78125000000000000)
  directionLo := (504900709286402255439/100000000000000000000)
  directionHi := (6311258866080028193/1250000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree103.table
  base := (23887632419546509161425567486255560058393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2147740057415519514857191950309204318000000000000)
      constant := (57399688692699676731706843915199255686845779697586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree103.table
  base := (23887632345407000652205441831619865870691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-239208349632817380191206749983325827000000000000)
      constant := (6407602773024738710426749109382977204134719118998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504900709286402255439/100000000000000000000)
  centralHi := (6311258866080028193/1250000000000000000)
  directionLo := (507369676133539142849/100000000000000000000)
  directionHi := (10147393522670782857/2000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree104.table
  base := (4944235110428432524136135979920900089431/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2168587522786942825285461321337853568000000000000)
      constant := (58538924279719107096715269313853024250137549262310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree104.table
  base := (4944235097738190099604172906434309363719/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-241530274144722922673380875134880952000000000000)
      constant := (6534767055895691865344762542849434174577769829910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507369676133539142849/100000000000000000000)
  centralHi := (10147393522670782857/2000000000000000000)
  directionLo := (25491334325697464059/5000000000000000000)
  directionHi := (509826686513949281181/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree105.table
  base := (6391790906275757187947408790147928648093/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-243270554239818459523747854707389202000000000000)
      constant := (6632155310419038251240246326399570357061822754216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree105.table
  base := (51134327141608516702210940027385034249013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-243852198656628465155555000286436077000000000000)
      constant := (6663185625240437422722982127753611368859138486157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25491334325697464059/5000000000000000000)
  centralHi := (509826686513949281181/100000000000000000000)
  directionLo := (256135956234054060431/50000000000000000000)
  directionHi := (512271912468108120863/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree106.table
  base := (52851193265701510135141757050091120775857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2210282453529789446142000063395152068000000000000)
      constant := (60851109234560369592147200300633158397412779385457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree106.table
  base := (26425596586388457672692540839435407752713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-246174123168534007637729125437991202000000000000)
      constant := (6792858481027380910041795397612742558112575830914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256135956234054060431/50000000000000000000)
  centralHi := (512271912468108120863/100000000000000000000)
  directionLo := (25735276097492782823/5000000000000000000)
  directionHi := (514705521949855656461/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree107.table
  base := (6824118642677594193101363761895343426987/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2231129918901212756570269434423801318000000000000)
      constant := (62024058601838103268461892596176385478299232804696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree107.table
  base := (54592949061914239164839470053474397882087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-248496047680439550119903250589546327000000000000)
      constant := (6923785623230069544038245279600173663802803981743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25735276097492782823/5000000000000000000)
  centralHi := (514705521949855656461/100000000000000000000)
  directionLo := (517127678961021827767/100000000000000000000)
  directionHi := (64640959870127728471/12500000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree108.table
  base := (56359594869542115816622294269674492059731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-250219709363626229666504311716938952000000000000)
      constant := (7023138432821890491741413415815452619621880304059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree108.table
  base := (56359594801522085008823666874527095463503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-250817972192345092602077375741101452000000000000)
      constant := (7055967051826397364863090975887278776337903095767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517127678961021827767/100000000000000000000)
  centralHi := (64640959870127728471/12500000000000000000)
  directionLo := (129884635920100739431/25000000000000000000)
  directionHi := (20781541747216118309/4000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree109.table
  base := (11630226088707240447992627952874061644221/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2272824849644059377426808176481099818000000000000)
      constant := (64403671115063859933272543529713424052839242965105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree109.table
  base := (58151130385348165307302100611249459320689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-253139896704250635084251500892656577000000000000)
      constant := (7189402766797932072306273888435453840904270713321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129884635920100739431/25000000000000000000)
  centralHi := (20781541747216118309/4000000000000000000)
  directionLo := (521938272587376261893/100000000000000000000)
  directionHi := (260969136293688130947/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree110.table
  base := (59967555857965970278769230280318652332749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2293672315015482687855077547509749068000000000000)
      constant := (65610334260694379823623433784018929748933014999949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree110.table
  base := (59967555808192944982017865545271248971871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-255461821216156177566425626044211702000000000000)
      constant := (7324092768129344974198470694322334453610234204519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521938272587376261893/100000000000000000000)
  centralHi := (260969136293688130947/50000000000000000000)
  directionLo := (524327018580422385231/100000000000000000000)
  directionHi := (32770438661276399077/6250000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree111.table
  base := (30904435554158682603170147380112617032233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-257168864487433999809260768726488702000000000000)
      constant := (7425359481352089286773193758516260184567877505474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree111.table
  base := (61808871065745911075288699140583861966441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-257783745728061720048599751195766827000000000000)
      constant := (7460037055807928294704780849870401549665783081249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524327018580422385231/100000000000000000000)
  centralHi := (32770438661276399077/6250000000000000000)
  directionLo := (526704931090810004911/100000000000000000000)
  directionHi := (32919058193175625307/6250000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree112.table
  base := (63675076190855858391862160310708238144971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2335367245758329308711616289567047568000000000000)
      constant := (68057374329388043700288278740235965867761124693771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree112.table
  base := (509400609235575580133478775638171530423/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-260105670239967262530773876347321952000000000000)
      constant := (7597235629823186494799247170735267807619151455875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526704931090810004911/100000000000000000000)
  centralHi := (32919058193175625307/6250000000000000000)
  directionLo := (264536078095840847023/50000000000000000000)
  directionHi := (529072156191681694047/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree113.table
  base := (65566171102504939593110118865465721054127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2356214711129752619139885660595696818000000000000)
      constant := (69297751252270471747580628548381518095550661919727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree113.table
  base := (32783085535684489305631166599837161884303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-262427594751872805012948001498877077000000000000)
      constant := (7735688490166490294823437966279593394109665893934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264536078095840847023/50000000000000000000)
  centralHi := (529072156191681694047/100000000000000000000)
  directionLo := (106285767340553277837/20000000000000000000)
  directionHi := (265714418351383194593/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree114.table
  base := (67482155840743215979528566143357553217627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-264118019611241769952017225736038452000000000000)
      constant := (7838818455638798678735537187028528803707800764803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree114.table
  base := (67482155814118630518034152089003702924551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-264749519263778347495122126650432202000000000000)
      constant := (7875395636830783815683851695601883928051136633039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106285767340553277837/20000000000000000000)
  centralHi := (265714418351383194593/50000000000000000000)
  directionLo := (33360944518183179369/6250000000000000000)
  directionHi := (106755022458186173981/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree115.table
  base := (34711515201758640210755541805923312297713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2397909641872599239996424402652995318000000000000)
      constant := (71812218874769710140664068833615170115412143568226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree115.table
  base := (69423030380752156288388488324512810412741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-267071443775683889977296251801987327000000000000)
      constant := (8016357069810336718382502300751346392361887201949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33360944518183179369/6250000000000000000)
  centralHi := (106755022458186173981/20000000000000000000)
  directionLo := (53611111956677057341/10000000000000000000)
  directionHi := (536111119566770573411/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree116.table
  base := (35694397394583971886598522175782696521789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2418757107244022550424693773681644568000000000000)
      constant := (73086309574288014908284851011669928700112039401978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree116.table
  base := (17847198692426072647694960847034287844797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-269393368287589432459470376953542452000000000000)
      constant := (8158572789100534461413379144547358548472318971732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53611111956677057341/10000000000000000000)
  centralHi := (536111119566770573411/100000000000000000000)
  directionLo := (538436992177428768211/100000000000000000000)
  directionHi := (134609248044357192053/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree117.table
  base := (18344862249091948065933884526802630373093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-271067174735049540094773682745588202000000000000)
      constant := (8263515355474320267339503823883134705595925477108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree117.table
  base := (36689724489864028309287990832371041741139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-271715292799494974941644502105097577000000000000)
      constant := (8302042794697700846169594606127533723776185466742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538436992177428768211/100000000000000000000)
  centralHi := (134609248044357192053/25000000000000000000)
  directionLo := (270376430447911270541/50000000000000000000)
  directionHi := (540752860895822541083/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree118.table
  base := (75394993024068341713309898225995521585253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2460452037986869171281232515738943068000000000000)
      constant := (75668204749684493411881395210668301075112722383653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree118.table
  base := (75394993009843849657128148896972273590009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-274037217311400517423818627256652702000000000000)
      constant := (8446767086598947910767544554202059491575696042801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270376430447911270541/50000000000000000000)
  centralHi := (540752860895822541083/100000000000000000000)
  directionLo := (271529426853222078927/50000000000000000000)
  directionHi := (108611770741288831571/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree119.table
  base := (15487085374291064719583102696017078975427/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (11567934)
      previous := (5783967)
      next := (5783967)
      square := (71087700824241360579858195812250000000000000)
      linear := (-8585811430305510317333916563209662000000000000)
      constant := (266352973098661740834098461335777450518274887215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree119.table
  base := (77435426859296377674074299130015634215243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7898633424915706731095355090250000000000000)
      linear := (-956260006309017508325234437398643000000000000)
      constant := (29732683961252764661158597913751072109629693843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271529426853222078927/50000000000000000000)
  centralHi := (108611770741288831571/20000000000000000000)
  directionLo := (109071019177579418491/20000000000000000000)
  directionHi := (68169386985987136557/12500000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree120.table
  base := (79500750537910861200795494039327760505173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-278016329858857310237530139755137952000000000000)
      constant := (8699450180748748608178496759757777978139934964397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree120.table
  base := (39750375263759128063601850618926690571521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-278681066335211602388166877559762952000000000000)
      constant := (8739978529305331374963803842628961176560609546738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109071019177579418491/20000000000000000000)
  centralHi := (68169386985987136557/12500000000000000000)
  directionLo := (273820855046158667657/50000000000000000000)
  directionHi := (109528342018463467063/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree121.table
  base := (40795482011490741656207289958059365072881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2522994434101139102566040628824890818000000000000)
      constant := (79625331953348944668175613390274900449830204139362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree121.table
  base := (4079548200704961895863166038881551686283/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-281002990847117144870341002711318077000000000000)
      constant := (8888465680107585629473861911809163079210247263740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273820855046158667657/50000000000000000000)
  centralHi := (109528342018463467063/20000000000000000000)
  directionLo := (137479704105455612637/25000000000000000000)
  directionHi := (549918816421822450549/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree122.table
  base := (83706067326351083349572918761743504589821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2543841899472562412994309999853540068000000000000)
      constant := (80966850205335477491695051357806546766324307218621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree122.table
  base := (83706067318760215099730441741095019298827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-283324915359022687352515127862873202000000000000)
      constant := (9038207117207988915543948975300609280849659591603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137479704105455612637/25000000000000000000)
  centralHi := (549918816421822450549/100000000000000000000)
  directionLo := (69023316562765401667/12500000000000000000)
  directionHi := (552186532502123213337/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree123.table
  base := (85846060447818067744679025800424664889681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-284965484982665080380286596764687702000000000000)
      constant := (9146622931410331900239222202840523208389954769609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree123.table
  base := (85846060441331260889948721740771689449461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-285646839870928229834689253014428327000000000000)
      constant := (9189202840606040273889414301330554980802372030029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69023316562765401667/12500000000000000000)
  centralHi := (552186532502123213337/100000000000000000000)
  directionLo := (554444973553425489457/100000000000000000000)
  directionHi := (277222486776712744729/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree124.table
  base := (11001367923409506590930677711899560614949/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2585536830215409033850848741910838568000000000000)
      constant := (83683600485418650840142791391510063222271035537192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree124.table
  base := (4400547169086654613857100615656630219037/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-287968764382833772316863378165983452000000000000)
      constant := (9341452850301505971138301845151305084516211405860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554444973553425489457/100000000000000000000)
  centralHi := (277222486776712744729/50000000000000000000)
  directionLo := (556694252458743285867/100000000000000000000)
  directionHi := (139173563114685821467/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree125.table
  base := (45100358072348783168153654381168689430777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2606384295586832344279118112939487818000000000000)
      constant := (85058832513511739797575147630095164030695218832754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree125.table
  base := (1127508951749517853477925643755539664487/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-290290688894739314799037503317538577000000000000)
      constant := (9494957146294373386571495292724143779540025227440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556694252458743285867/100000000000000000000)
  centralHi := (139173563114685821467/25000000000000000000)
  directionLo := (558934479829737574527/100000000000000000000)
  directionHi := (4366675623669824801/781250000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree126.table
  base := (18483075744024059065735938599339666328551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-291914640106472850523043053774237452000000000000)
      constant := (9605033607441472656631655129977244389834357945195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree126.table
  base := (23103844679018449779163195300642661273341/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-292612613406644857281211628469093702000000000000)
      constant := (9649715728584812124407850101856708805022650381396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558934479829737574527/100000000000000000000)
  centralHi := (4366675623669824801/781250000000000000)
  directionLo := (561165764070189543931/100000000000000000000)
  directionHi := (140291441017547385983/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree127.table
  base := (47327465556817743436915278038934865141699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2648079226329678965135656854996786318000000000000)
      constant := (87843010345805614219456037684186387156033072737798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree127.table
  base := (47327465555089214805739561877421184237123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-294934537918550399763385753620648827000000000000)
      constant := (9805728597173141241046025729795633027857871415894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (561165764070189543931/100000000000000000000)
  centralHi := (140291441017547385983/25000000000000000000)
  directionLo := (563388211437211338329/100000000000000000000)
  directionHi := (56338821143721133833/10000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree128.table
  base := (48459686662689087215376050077357923016033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20544345538205753207579018589740250000000000000)
      linear := (-2668926691701102275563926226025435568000000000000)
      constant := (89251956150012403542784353933436315058315446796866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree128.table
  base := (96919373322424877678704376529965435440371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-297256462430455942245559878772203952000000000000)
      constant := (9962995752059801646533019044421123126601967901019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell073.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563388211437211338329/100000000000000000000)
  centralHi := (56338821143721133833/10000000000000000000)
  directionLo := (565601926100292079979/100000000000000000000)
  directionHi := (28280096305014603999/5000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree129.table
  base := (9920870535551894766459337280243992279233/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-298863795230280620665799510783787202000000000000)
      constant := (10074682208844238677923100136910820380044917357370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree129.table
  base := (99208705352996157663872028995483399428563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2282705059800639245286557621082250000000000000)
      linear := (-299578386942361484727734003923759077000000000000)
      constant := (10121517193245332883447769006054060108162952866107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell073.Kernel129
