import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell070.Parameters
import ForestUnimodality.BinomialMassData.Q405_808.Batch000_049
import ForestUnimodality.BinomialMassData.Q405_808.Batch050_099
import ForestUnimodality.BinomialMassData.Q405_808.Batch100_149
import ForestUnimodality.BinomialMassData.Q405_808.Batch150_199
import ForestUnimodality.BinomialMassData.Q203_404.Batch000_049
import ForestUnimodality.BinomialMassData.Q203_404.Batch050_099
import ForestUnimodality.BinomialMassData.Q203_404.Batch100_149
import ForestUnimodality.BinomialMassData.Q203_404.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree000.table
  base := (93661201301712513263275639/1250000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (28606160151293580362619195600000000000)
      linear := (-186576699295048749685510536000000000)
      constant := (29971584416548004244248204480000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree000.table
  base := (93661201301712513263275639/1250000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (28606160151293580362619195600000000000)
      linear := (-186576699295048749685510536000000000)
      constant := (29971584416548004244248204480000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree001.table
  base := (419043191104941886211829886908132063492549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-7360925353916869211969411049555900000000000)
      constant := (4276516303702876728618683590422546835937492349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree001.table
  base := (418230203951002338473964299787092459532153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-7378982992512373284573314416778400000000000)
      constant := (4268232142975951796477944794818065854687492753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12499846827803811301/25000000000000000000)
  directionHi := (9999877462243049041/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree002.table
  base := (123105153357806449714321287897876260599451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-14674268985096018616550274774668400000000000)
      constant := (2518970484272146226751898785680268843749999302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree002.table
  base := (61340633214789814534351699806636811801539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-14710384262287026761758081509113400000000000)
      constant := (2510358710307570779273391624388256068749997356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12499846827803811301/25000000000000000000)
  centralHi := (9999877462243049041/20000000000000000000)
  directionLo := (35354905822932919159/50000000000000000000)
  directionHi := (70709811645865838319/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree003.table
  base := (153709618884833936777975542569020954688601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-21987612616275168021131138499780900000000000)
      constant := (1584559124918634465997655377491899915028418801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree003.table
  base := (15303287231341303374574326786246796308689/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-4408357106412336047788569720289680000000000)
      constant := (315547474177531418633267350765994293289872978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35354905822932919159/50000000000000000000)
  centralHi := (70709811645865838319/100000000000000000000)
  directionLo := (86601479170339441739/100000000000000000000)
  directionHi := (4330073958516972087/5000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree004.table
  base := (102532259688448288816619475425961412313129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-29300956247454317425712002224893400000000000)
      constant := (1075352763948018853325775176165483367006228929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree004.table
  base := (25509347688368321144852213646280352947331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-29373186801836333716127615693783400000000000)
      constant := (1070449838969688564436499136972823721662894124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86601479170339441739/100000000000000000000)
  centralHi := (4330073958516972087/5000000000000000000)
  directionLo := (99998774622430490409/100000000000000000000)
  directionHi := (9999877462243049041/10000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree005.table
  base := (36445480226236862111099286826914960413729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-36614299878633466830292865950005900000000000)
      constant := (789501473617006647016702638630317928610899058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree005.table
  base := (72537270204606534581509786450914160568729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-36704588071610987193312382786118400000000000)
      constant := (786120332393409003827505396019216226961604529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99998774622430490409/100000000000000000000)
  centralHi := (9999877462243049041/10000000000000000000)
  directionLo := (111802028861217721361/100000000000000000000)
  directionHi := (55901014430608860681/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree006.table
  base := (13670623496384404907864489699374627333587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-43927643509812616234873729675118400000000000)
      constant := (623942233346405716141874749765643168719683948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree006.table
  base := (27213286447976856492143211224713177816249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-44035989341385640670497149878453400000000000)
      constant := (621658179958285030437439433021856053807112098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111802028861217721361/100000000000000000000)
  centralHi := (55901014430608860681/50000000000000000000)
  directionLo := (30618246591066282437/25000000000000000000)
  directionHi := (122472986364265129749/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree007.table
  base := (42723624912502292145195194760645905537397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-51240987140991765639454593400230900000000000)
      constant := (525800859074436557446527458952885788636986797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree007.table
  base := (42532245373648177733368232896083216624569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-51367390611160294147681916970788400000000000)
      constant := (524293063381423028669667474668395867787228369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30618246591066282437/25000000000000000000)
  centralHi := (122472986364265129749/100000000000000000000)
  directionLo := (66142972265536994977/50000000000000000000)
  directionHi := (26457188906214797991/20000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree008.table
  base := (3432182785828912979740462925868414129543/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-11710866154434183008807091425068680000000000)
      constant := (93522179889984450053087421447392785070936286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree008.table
  base := (17086297014434741983832897088042356898849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-58698791880934947624866684063123400000000000)
      constant := (466669026159245640496216310664260565450317298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66142972265536994977/50000000000000000000)
  centralHi := (26457188906214797991/20000000000000000000)
  directionLo := (141419623291731676637/100000000000000000000)
  directionHi := (70709811645865838319/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree009.table
  base := (3506653826177769686408606918161653078833/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-65867674403350064448616320850455900000000000)
      constant := (434847434023194372635969326358467340707403464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree009.table
  base := (13965999379631431342711814888716783256007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-66030193150709601102051451155458400000000000)
      constant := (434345327627631867330178325110565886989054814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141419623291731676637/100000000000000000000)
  centralHi := (70709811645865838319/50000000000000000000)
  directionLo := (74999080966822867807/50000000000000000000)
  directionHi := (29999632386729147123/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree010.table
  base := (723275511023071433510079982451109621511/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-73181018034529213853197184575568400000000000)
      constant := (419624918283176250053223452467029990969078752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree010.table
  base := (2880369638875810935628536889004897805413/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-73361594420484254579236218247793400000000000)
      constant := (419492675255145258048694769764199700104144104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74999080966822867807/50000000000000000000)
  centralHi := (29999632386729147123/20000000000000000000)
  directionLo := (79055972758181150399/50000000000000000000)
  directionHi := (158111945516362300799/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree011.table
  base := (9580539640551363656090086058369381006173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-80494361665708363257778048300680900000000000)
      constant := (417500757491285913920038291895233767537941546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree011.table
  base := (19073392536349960292760384363146084996839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-80692995690258908056420985340128400000000000)
      constant := (417703456178184001901753985888439388052754639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79055972758181150399/50000000000000000000)
  centralHi := (158111945516362300799/100000000000000000000)
  directionLo := (82914603729478850989/50000000000000000000)
  directionHi := (165829207458957701979/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree012.table
  base := (7922233054443283875554587017523179768843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-87807705296887512662358912025793400000000000)
      constant := (425847650580822811913082414803135913643934886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree012.table
  base := (15767788234610103058844019460824810988979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-88024396960033561533605752432463400000000000)
      constant := (426371143512978999603592241291934496898574779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82914603729478850989/50000000000000000000)
  centralHi := (165829207458957701979/100000000000000000000)
  directionLo := (86601479170339441739/50000000000000000000)
  directionHi := (173202958340678883479/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree013.table
  base := (6516801338052182305467025728698336960391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-95121048928066662066939775750905900000000000)
      constant := (443019419745775444292387405570191876915897182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree013.table
  base := (2593188364394768930413079353467686921509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-19071159645961643002158103904959680000000000)
      constant := (88772302548450622508939505013226129286313309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86601479170339441739/50000000000000000000)
  centralHi := (173202958340678883479/100000000000000000000)
  directionLo := (90137677346185064761/50000000000000000000)
  directionHi := (180275354692370129523/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree014.table
  base := (1062095713400551422323434074598342217839/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-20486878511849162294304127895203680000000000)
      constant := (93583826519407780607279222925427952928351278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree014.table
  base := (10560982068139988926446528113250050568103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-102687199499582868487975286617133400000000000)
      constant := (469084370445703838839948379894601965845218703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90137677346185064761/50000000000000000000)
  centralHi := (180275354692370129523/100000000000000000000)
  directionLo := (3741611537343595959/2000000000000000000)
  directionHi := (187080576867179797951/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree015.table
  base := (2132643523824526566943238027302992294591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-109747736190424960876101503201130900000000000)
      constant := (499771968228848410968369989009922703838491164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree015.table
  base := (1695464640536586961951986679074488728871/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-22003720153871504393032010741893680000000000)
      constant := (100253733235843924390310456248947134523213071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3741611537343595959/2000000000000000000)
  centralHi := (187080576867179797951/100000000000000000000)
  directionLo := (48411698594227770219/25000000000000000000)
  directionHi := (193646794376911080877/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree016.table
  base := (209565205293234732587099030183115378453/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-117061079821604110280682366926243400000000000)
      constant := (538002926970107350581027556873488719219169696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree016.table
  base := (416175464963514108038315729543934964751/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-117350002039132175442344820801803400000000000)
      constant := (539841534365912418374331714957363689206799216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48411698594227770219/25000000000000000000)
  centralHi := (193646794376911080877/100000000000000000000)
  directionLo := (199997549244860980819/100000000000000000000)
  directionHi := (9999877462243049041/5000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree017.table
  base := (2552020958744934125895815749746276855447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-124374423452783259685263230651355900000000000)
      constant := (582168748452703962748721662730394196654829694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree017.table
  base := (1265526383414101802506575259848212148837/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-124681403308906828919529587894138400000000000)
      constant := (584360973380766309029421966010922923521144948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199997549244860980819/100000000000000000000)
  centralHi := (9999877462243049041/5000000000000000000)
  directionLo := (206152755100307852147/100000000000000000000)
  directionHi := (51538188775076963037/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree018.table
  base := (3690016611902147617430442104157710301313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-131687767083962409089844094376468400000000000)
      constant := (631918278270417235853344795102314177783693913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree018.table
  base := (913218191055766237814623498123686540323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-132012804578681482396714354986473400000000000)
      constant := (634476632723019887614560180687847305591339692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206152755100307852147/100000000000000000000)
  centralHi := (51538188775076963037/25000000000000000000)
  directionLo := (53032358734399378739/25000000000000000000)
  directionHi := (212129434937597514957/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree019.table
  base := (2436227591696281427836328506669012412637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-139001110715141558494424958101580900000000000)
      constant := (686968101418760751085738909530476751871310037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree019.table
  base := (2403382313123481021715263753870220339477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-139344205848456135873899122078808400000000000)
      constant := (689905671122329438519753223484346692683004877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53032358734399378739/25000000000000000000)
  centralHi := (212129434937597514957/100000000000000000000)
  directionLo := (43588455305707418143/20000000000000000000)
  directionHi := (54485569132134272679/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree020.table
  base := (131997284011055820646336061893209941019/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-29262890869264141579801164365338680000000000)
      constant := (149417326924949657934731794637246269216669638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree020.table
  base := (1290977161792397972498900432839963905869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-146675607118230789351083889171143400000000000)
      constant := (750416964332310770508795555805601471803769669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43588455305707418143/20000000000000000000)
  centralHi := (54485569132134272679/25000000000000000000)
  directionLo := (223604057722435442723/100000000000000000000)
  directionHi := (55901014430608860681/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree021.table
  base := (322551571940125686204012571910585551719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-153627797977499857303586685551805900000000000)
      constant := (812083111178505153640341114679537789463085519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree021.table
  base := (148497904464791564438167674869029470763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-154007008388005442828268656263478400000000000)
      constant := (815820146378200210066735144050339614262506726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223604057722435442723/100000000000000000000)
  centralHi := (55901014430608860681/25000000000000000000)
  directionLo := (114562988527529205487/50000000000000000000)
  directionHi := (9165039082202336439/4000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree022.table
  base := (-571523065905513907457065470086740427541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-160941141608679006708167549276918400000000000)
      constant := (881799549691655175187954250336510035898654259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree022.table
  base := (-594012520781768880133794869063282001829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-161338409657780096305453423355813400000000000)
      constant := (885957603900991025604191100444184060299342371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114562988527529205487/50000000000000000000)
  centralHi := (9165039082202336439/4000000000000000000)
  directionLo := (234517914226039596771/100000000000000000000)
  directionHi := (58629478556509899193/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree023.table
  base := (-42972563212788245848468744827255713619/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-168254485239858156112748413002030900000000000)
      constant := (956104653609543765868368260491215169141922592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree023.table
  base := (-1394884904236410536250226126205950922643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-168669810927554749782638190448148400000000000)
      constant := (960698385879279847055150600044284869638118757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234517914226039596771/100000000000000000000)
  centralHi := (58629478556509899193/25000000000000000000)
  directionLo := (239788637813448069871/100000000000000000000)
  directionHi := (14986789863340504367/6250000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree024.table
  base := (-16791747851044563839484836965847555711/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4080400000000000000000000000000000000000000
      center := (61206)
      previous := (30603)
      next := (30603)
      square := (291811439703345813279078414315600000000000)
      linear := (-7022713154841492220693171069085736000000000)
      constant := (41395561429854829599492255340592185420960445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree024.table
  base := (-84652502292814057835268207632430184751/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4080400000000000000000000000000000000000000
      center := (61206)
      previous := (30603)
      next := (30603)
      square := (291811439703345813279078414315600000000000)
      linear := (-7040048487893176130392918301619336000000000)
      constant := (41597337248792539616985520682353627685355049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239788637813448069871/100000000000000000000)
  centralHi := (14986789863340504367/6250000000000000000)
  directionLo := (244945972728530259497/100000000000000000000)
  directionHi := (122472986364265129749/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree025.table
  base := (-1376006031932169557370369371977875803187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-182881172502216454921910140452255900000000000)
      constant := (1118061401005617041996315128614417534113378826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree025.table
  base := (-1383607514726063848683019659326700744753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-183332613467104056737007724632818400000000000)
      constant := (1123571751598973469075519379671683526405549294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244945972728530259497/100000000000000000000)
  centralHi := (122472986364265129749/50000000000000000000)
  directionLo := (31249617069509528253/12500000000000000000)
  directionHi := (9999877462243049041/4000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree026.table
  base := (-1670866095523146377359107972624764132119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-190194516133395604326491004177368400000000000)
      constant := (1205545451815847103704262843817062937176508162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree026.table
  base := (-3355043636539590019513157007048702715233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-190664014736878710214192491725153400000000000)
      constant := (1211537336143183797723204607281704983601908167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31249617069509528253/12500000000000000000)
  centralHi := (9999877462243049041/4000000000000000000)
  directionLo := (254947851567570017351/100000000000000000000)
  directionHi := (31868481445946252169/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree027.table
  base := (-387438630555595803144617609933927798659/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-39501571952914950746214373580496180000000000)
      constant := (259455471200959424788484184852130136301759082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree027.table
  base := (-971507438467662212209740616849694243587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-197995416006653363691377258817488400000000000)
      constant := (1303766618593132502004794961028392051084676052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254947851567570017351/100000000000000000000)
  centralHi := (31868481445946252169/12500000000000000000)
  directionLo := (259804437511018325217/100000000000000000000)
  directionHi := (129902218755509162609/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree028.table
  base := (-4355214234771925438146103537332904326457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-204821203395753903135652731627593400000000000)
      constant := (1393203662093378101089437008283549042965812143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree028.table
  base := (-1091347302542738464433067810175763195179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-205326817276428017168562025909823400000000000)
      constant := (1400206392279989229612252133578009558583916084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259804437511018325217/100000000000000000000)
  centralHi := (129902218755509162609/50000000000000000000)
  directionLo := (264571889062147979909/100000000000000000000)
  directionHi := (26457188906214797991/10000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree029.table
  base := (-95772142815943774744303912178598875417/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4080400000000000000000000000000000000000000
      center := (61206)
      previous := (30603)
      next := (30603)
      square := (291811439703345813279078414315600000000000)
      linear := (-8485381881077322101609343814108236000000000)
      constant := (59731183033479095831003891428858921993742366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree029.table
  base := (-599686402921376158182381572936721850291/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-212658218546202670645746793002158400000000000)
      constant := (1500812086811644907004843972544672078241452072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264571889062147979909/100000000000000000000)
  centralHi := (26457188906214797991/10000000000000000000)
  directionLo := (16828433807915238377/6250000000000000000)
  directionHi := (269254940926643814033/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree030.table
  base := (-2589123797208561891543432565384686513231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-219447890658112201944814459077818400000000000)
      constant := (1597467531331013388908326512431888500757061138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree030.table
  base := (-259299920992141218774205102446329321133/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-43997923963195464824586312018898680000000000)
      constant := (321109267947295733455585219698127778380489068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16828433807915238377/6250000000000000000)
  centralHi := (269254940926643814033/100000000000000000000)
  directionLo := (273857922917901650441/100000000000000000000)
  directionHi := (136928961458950825221/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree031.table
  base := (-5527225948540380975686517847261916406163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-226761234289291351349395322802930900000000000)
      constant := (1705736003885464937759485624416061596990731237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree031.table
  base := (-5533983121567538196046075594448817459889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-227321021085751977600116327186828400000000000)
      constant := (1714377810297960911408455981993989788091672311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273857922917901650441/100000000000000000000)
  centralHi := (136928961458950825221/50000000000000000000)
  directionLo := (278384806834719832723/100000000000000000000)
  directionHi := (69596201708679958181/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree032.table
  base := (-364883573315120975910689487640489525451/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-234074577920470500753976186528043400000000000)
      constant := (1818058522212637419297794908748777861613989584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree032.table
  base := (-2922012036301665301587046909629287551531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-234652422355526631077301094279163400000000000)
      constant := (1827280192727954146481060563822304875373664538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278384806834719832723/100000000000000000000)
  centralHi := (69596201708679958181/25000000000000000000)
  directionLo := (141419623291731676637/50000000000000000000)
  directionHi := (11313569863338534131/4000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree033.table
  base := (-305658076640670612145921502432483718323/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-48277584310329930031711410050631180000000000)
      constant := (386882569086074274311659070453434865607548308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree033.table
  base := (-1223657399010952394533797312230992188589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-48396764725060256910897172274299680000000000)
      constant := (388846278899053950420439115760039103684203611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141419623291731676637/50000000000000000000)
  centralHi := (11313569863338534131/4000000000000000000)
  directionLo := (287224612697794577817/100000000000000000000)
  directionHi := (143612306348897288909/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree034.table
  base := (-6354131876012449033287187997321741153441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-248701265182828799563137913978268400000000000)
      constant := (2054780276654610727542717947305126293493748359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree034.table
  base := (-6358591748369530791898206078561733421501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-249315224895075938031670628463833400000000000)
      constant := (2065212851213681756002225646439480957367268299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287224612697794577817/100000000000000000000)
  centralHi := (143612306348897288909/50000000000000000000)
  directionLo := (145772011091717303553/50000000000000000000)
  directionHi := (291544022183434607107/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree035.table
  base := (-20508093147012508638481243966490385581/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-51202921762801589793543755540676180000000000)
      constant := (435829017995764104630437958895176252158046016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree035.table
  base := (-262658734869803109619037370280957818901/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4080400000000000000000000000000000000000000
      center := (61206)
      previous := (30603)
      next := (30603)
      square := (291811439703345813279078414315600000000000)
      linear := (-10265865046594023660354215822246736000000000)
      constant := (87608358198133482632336259893028644289390899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145772011091717303553/50000000000000000000)
  centralHi := (291544022183434607107/100000000000000000000)
  directionLo := (73950091109811995603/25000000000000000000)
  directionHi := (295800364439247982413/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree036.table
  base := (-3369916310021301129644045178760364933641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-263327952445187098372299641428493400000000000)
      constant := (2307494051705534429860337457600690034623856318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree036.table
  base := (-6743203889258773303858734112278040466817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-263978027434625244986040162648503400000000000)
      constant := (2319206576781622425198595732135373509197999783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73950091109811995603/25000000000000000000)
  centralHi := (295800364439247982413/100000000000000000000)
  directionLo := (74999080966822867807/25000000000000000000)
  directionHi := (299996323867291471229/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree037.table
  base := (-860869067922461252505539431651133850713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-270641296076366247776880505153605900000000000)
      constant := (2439816020013135362705943625799171174961013496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree037.table
  base := (-6889881430929155339921030055470079628599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-271309428704399898463224929740838400000000000)
      constant := (2452194667689218729484616347450352192708661601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74999080966822867807/25000000000000000000)
  centralHi := (299996323867291471229/100000000000000000000)
  directionLo := (30413439967452834403/10000000000000000000)
  directionHi := (304134399674528344031/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree038.table
  base := (-7004869579138964716304939564886695210711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-277954639707545397181461368878718400000000000)
      constant := (2576101609960367511559171461477959697155537089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree038.table
  base := (-1401482591083053488887020799931846319901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-55728165994834910388081939366634680000000000)
      constant := (517832784957169014989199059095107115690689899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30413439967452834403/10000000000000000000)
  centralHi := (304134399674528344031/100000000000000000000)
  directionLo := (308216923281124618007/100000000000000000000)
  directionHi := (38527115410140577251/12500000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree039.table
  base := (-3547179501131270586028202091807064331401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-285267983338724546586042232603830900000000000)
      constant := (2716342912967546363100535274986747179760756798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree039.table
  base := (-7096566640116234129805008083919986524563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-285972231243949205417594463925508400000000000)
      constant := (2730106511893852992431698840340224792462932837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308216923281124618007/100000000000000000000)
  centralHi := (38527115410140577251/12500000000000000000)
  directionLo := (312246073679685475449/100000000000000000000)
  directionHi := (6244921473593709509/2000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree040.table
  base := (-1431214880664776934440048941486180545697/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-58516265393980739198124619265788680000000000)
      constant := (572106652351446399591750900746026472253344903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree040.table
  base := (-7157989823160054728692615819995087784207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-293303632513723858894779231017843400000000000)
      constant := (2875015825516998760749243210351132109513304393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312246073679685475449/100000000000000000000)
  centralHi := (6244921473593709509/2000000000000000000)
  directionLo := (79055972758181150399/25000000000000000000)
  directionHi := (316223891032724601597/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree041.table
  base := (-7190567009595395697538370144234309334681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-299894670601082845395203960054055900000000000)
      constant := (3008667033260018658829168873918554966726919119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree041.table
  base := (-7192228232099502450468172388483234917833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-300635033783498512371963998110178400000000000)
      constant := (3023886298688516540389842534420970195603185567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79055972758181150399/25000000000000000000)
  centralHi := (316223891032724601597/100000000000000000000)
  directionLo := (320152288749234767617/100000000000000000000)
  directionHi := (160076144374617383809/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree042.table
  base := (-719830189559103947342459639903355208281/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-61441602846452398959956964755833680000000000)
      constant := (632147896650157877289588821901003222040651038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree042.table
  base := (-7199742110374653936432520136642971609491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-307966435053273165849148765202513400000000000)
      constant := (3176713236465074109535586919765354646611582309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320152288749234767617/100000000000000000000)
  centralHi := (160076144374617383809/50000000000000000000)
  directionLo := (324033064243250193093/100000000000000000000)
  directionHi := (162016532121625096547/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree043.table
  base := (-1435934318398149716907559632605821273351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-62904271572688228840873137500856180000000000)
      constant := (663349321504815637703754201952915948440546449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree043.table
  base := (-1436183950028626456651949500509268138363/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-63059567264609563865266706458969680000000000)
      constant := (666698535575674310995460798045502510720559037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (324033064243250193093/100000000000000000000)
  centralHi := (162016532121625096547/50000000000000000000)
  directionLo := (163933954273029736873/50000000000000000000)
  directionHi := (327867908546059473747/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree044.table
  base := (-891875939631949757024648881315854477867/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-321834701494620293608946551229393400000000000)
      constant := (3476685025282203838708368256215711747770229864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree044.table
  base := (-7136088855161695156768430551618670266241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-322629237592822472803518299387183400000000000)
      constant := (3494221280022386191765978451364040144614075559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163933954273029736873/50000000000000000000)
  centralHi := (327867908546059473747/100000000000000000000)
  directionLo := (82914603729478850989/25000000000000000000)
  directionHi := (331658414917915403957/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree045.table
  base := (-7064589584263777113699033388623383413539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-329148045125799443013527414954505900000000000)
      constant := (3640551881127775328729488717663699272048488661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree045.table
  base := (-3532763043476250912612291535584867948927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-329960638862597126280703066479518400000000000)
      constant := (3658896220672930473206028696530590399105991346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82914603729478850989/25000000000000000000)
  centralHi := (331658414917915403957/100000000000000000000)
  directionLo := (83851521645913291021/25000000000000000000)
  directionHi := (67081217316730632817/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree046.table
  base := (-6968654281430177333701729694358998827379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-336461388756978592418108278679618400000000000)
      constant := (3808344762648592949608640009630214727961906821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree046.table
  base := (-6969465088984292366627443849209786420569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-337292040132371779757887833571853400000000000)
      constant := (3827515116432979781761784490850670768723775631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83851521645913291021/25000000000000000000)
  centralHi := (67081217316730632817/20000000000000000000)
  directionLo := (169556171849374119961/50000000000000000000)
  directionHi := (339112343698748239923/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree047.table
  base := (-1369480293591426327746585337724603864389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-68754946477631548364537828480946180000000000)
      constant := (796012326215778700640623521583093197229367811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree047.table
  base := (-3424051617486486258321953336745401856839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-344623441402146433235072600664188400000000000)
      constant := (4000075953893258163023707850795423286316770722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169556171849374119961/50000000000000000000)
  centralHi := (339112343698748239923/100000000000000000000)
  directionLo := (342778529637366387909/100000000000000000000)
  directionHi := (34277852963736638791/10000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree048.table
  base := (-6701000096405347552585885574182362686701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-351088076019336891227270006129843400000000000)
      constant := (4155700762933605212062706454990027718232963099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree048.table
  base := (-6701607306954987717814134239975432211921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-351954842671921086712257367756523400000000000)
      constant := (4176577031710211837032446576703333016006193879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342778529637366387909/100000000000000000000)
  centralHi := (34277852963736638791/10000000000000000000)
  directionLo := (346405916681357766957/100000000000000000000)
  directionHi := (173202958340678883479/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree049.table
  base := (-3264796515437779298818529181576040215987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-358401419650516040631850869854955900000000000)
      constant := (4335260700856036493525644363878314283763433226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree049.table
  base := (-3265059137553914929045919965489908053807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-359286243941695740189442134848858400000000000)
      constant := (4357016911847060209038984838361392970886229586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346405916681357766957/100000000000000000000)
  centralHi := (173202958340678883479/50000000000000000000)
  directionLo := (349995711178506716433/100000000000000000000)
  directionHi := (174997855589253358217/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree050.table
  base := (-253332044264020442054604688530409739677/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4080400000000000000000000000000000000000000
      center := (61206)
      previous := (30603)
      next := (30603)
      square := (291811439703345813279078414315600000000000)
      linear := (-14628590531267807601457269343202736000000000)
      constant := (180749608488239124112614855995973665245554923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree050.table
  base := (-6333755323228407167629170891435267770567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-366617645211470393666626901941193400000000000)
      constant := (4541394378509891018187540582744158833472446033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349995711178506716433/100000000000000000000)
  centralHi := (174997855589253358217/50000000000000000000)
  directionLo := (353549058229329191593/100000000000000000000)
  directionHi := (176774529114664595797/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree051.table
  base := (-6112226551711912372971958644584175605997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-373028106912874339441012597305180900000000000)
      constant := (4706138254154258492140569016651800980893224603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree051.table
  base := (-6112619240376961744320209339546009111003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-373949046481245047143811669033528400000000000)
      constant := (4729708403549500734837496277143729336058658397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353549058229329191593/100000000000000000000)
  centralHi := (176774529114664595797/50000000000000000000)
  directionLo := (178533522977018601317/50000000000000000000)
  directionHi := (71413409190807440527/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree052.table
  base := (-5866455872581122804773995716992061369671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-380341450544053488845593461030293400000000000)
      constant := (4897453944249383415669367484511976981967986129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree052.table
  base := (-1173359055932533379028404547730113699277/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-76256089550203940124199287225172680000000000)
      constant := (984391623459784536416875771273317630153675323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178533522977018601317/50000000000000000000)
  centralHi := (71413409190807440527/20000000000000000000)
  directionLo := (72110141876948051809/20000000000000000000)
  directionHi := (180275354692370129523/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree053.table
  base := (-111921245755692402084294043928965460891/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4080400000000000000000000000000000000000000
      center := (61206)
      previous := (30603)
      next := (30603)
      square := (291811439703345813279078414315600000000000)
      linear := (-15506191767009305530006972990216236000000000)
      constant := (203707461423546168951923437103730682916901818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree053.table
  base := (-1399088892208568925247540702184077909251/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-388611849020794354098181203218198400000000000)
      constant := (5118142783982991829749972797317144159990922196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72110141876948051809/20000000000000000000)
  centralHi := (180275354692370129523/50000000000000000000)
  directionLo := (364001034022344968907/100000000000000000000)
  directionHi := (91000258505586242227/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree054.table
  base := (-662638472759544599781534122480182185819/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-394968137806411787654755188480518400000000000)
      constant := (5291835395865595846799223799752510167179683048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree054.table
  base := (-5301361143704816211071989184258741470341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-395943250290569007575365970310533400000000000)
      constant := (5318261780975379478704313824364316778261051459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (364001034022344968907/100000000000000000000)
  centralHi := (91000258505586242227/25000000000000000000)
  directionLo := (73483791818559077849/20000000000000000000)
  directionHi := (183709479546397694623/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree055.table
  base := (-996328968062400090674928182660328881737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-80456296287518187411867210441126180000000000)
      constant := (1098979997936439123965407539605266766327400863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree055.table
  base := (-4981863664035495336123311795393295403341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-403274651560343661052550737402868400000000000)
      constant := (5522314581294861557250985940410386368590518459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73483791818559077849/20000000000000000000)
  centralHi := (183709479546397694623/50000000000000000000)
  directionLo := (370805380533144588443/100000000000000000000)
  directionHi := (92701345133286147111/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree056.table
  base := (-1159429477923434931607257859295281089701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-409594825068770086463916915930743400000000000)
      constant := (5701879863612142016393029075697704350415840396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree056.table
  base := (-2318953430979608158490034757341696419657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-410606052830118314529735504495203400000000000)
      constant := (5730300738829950319430221733016537509646157886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370805380533144588443/100000000000000000000)
  centralHi := (92701345133286147111/25000000000000000000)
  directionLo := (3741611537343595959/1000000000000000000)
  directionHi := (374161153734359595901/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree057.table
  base := (-2134682323340383120153351677986133304441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-416908168699949235868497779655855900000000000)
      constant := (5912774633583100822752084201701995064572794718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree057.table
  base := (-2134763882515022717617255568363045325861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-417937454099892968006920271587538400000000000)
      constant := (5942219875862566735103498672229085624261783878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3741611537343595959/1000000000000000000)
  centralHi := (374161153734359595901/100000000000000000000)
  directionLo := (9437177401616305973/2500000000000000000)
  directionHi := (377487096064652238921/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree058.table
  base := (-3876616942183615164544823039688978193581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-424221512331128385273078643380968400000000000)
      constant := (6127583974214687669639754441898694108447280219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree058.table
  base := (-969189432321334868416707694437820401873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-425268855369667621484105038679873400000000000)
      constant := (6158071672529773727729675997868369576321974108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9437177401616305973/2500000000000000000)
  centralHi := (377487096064652238921/100000000000000000000)
  directionLo := (2974874915581454799/781250000000000000)
  directionHi := (380783989194426214273/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree059.table
  base := (-3459501825017216993738450783580027875533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-431534855962307534677659507106080900000000000)
      constant := (6346307609806363451080675586215968791891687867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree059.table
  base := (-3459623312088970416524344627244586882247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-432600256639442274961289805772208400000000000)
      constant := (6377855857919902439197446837485446544214198353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2974874915581454799/781250000000000000)
  centralHi := (380783989194426214273/100000000000000000000)
  directionLo := (96013145310394155677/25000000000000000000)
  directionHi := (384052581241576622709/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree060.table
  base := (-754510549712597568149812421695914229443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-438848199593486684082240370831193400000000000)
      constant := (6568945306717802549100243959379509915781807828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree060.table
  base := (-377268376226224530944694971514249581043/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-439931657909216928438474572864543400000000000)
      constant := (6601572202547494149214572268286768120190242856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96013145310394155677/25000000000000000000)
  centralHi := (384052581241576622709/100000000000000000000)
  directionLo := (48411698594227770219/12500000000000000000)
  directionHi := (387293588753822161753/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree061.table
  base := (-2552257475910771676996902361268469871699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-446161543224665833486821234556305900000000000)
      constant := (6795496866924870841967912929064625745088798501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree061.table
  base := (-2552347881431486202136498357826874479939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-447263059178991581915659339956878400000000000)
      constant := (6829220511991856447911042694366421728430142261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48411698594227770219/12500000000000000000)
  centralHi := (387293588753822161753/100000000000000000000)
  directionLo := (15620307941718006277/4000000000000000000)
  directionHi := (195253849271475078463/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree062.table
  base := (-2062164111360561144756595438721621672773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-453474886855844982891402098281418400000000000)
      constant := (7025962122568458728117927766441475612316042627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree062.table
  base := (-515560518966212867354520549166303908427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-454594460448766235392844107049213400000000000)
      constant := (7060800621517950150346268356317318735320544692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15620307941718006277/4000000000000000000)
  centralHi := (195253849271475078463/50000000000000000000)
  directionLo := (393695569384275072999/100000000000000000000)
  directionHi := (393695569384275073/100000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree063.table
  base := (-193472006930883670762550326690532765597/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-460788230487024132295982962006530900000000000)
      constant := (7260340931342093391199333097753677408315160024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree063.table
  base := (-309568655587840460192774323045615190991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-92385172343708177774005774828309680000000000)
      constant := (1459262478305366292528813955449564434436700809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393695569384275072999/100000000000000000000)
  centralHi := (393695569384275073/100000000000000000)
  directionLo := (49607229199152746233/12500000000000000000)
  directionHi := (79371566718644393973/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree064.table
  base := (-50455256808347900965822944850092860263/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-93620314823640656340112765146328680000000000)
      constant := (1499726634517676177086382331550140010929828548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree064.table
  base := (-1009163085699155479195652164559498978727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-469257262988315542347213641233883400000000000)
      constant := (7535755703706847249006962322751731750918005873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49607229199152746233/12500000000000000000)
  centralHi := (79371566718644393973/20000000000000000000)
  directionLo := (199997549244860980819/50000000000000000000)
  directionHi := (399995098489721961639/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree065.table
  base := (-446161383192430424736655263608657323383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-475414917749382431105144689456755900000000000)
      constant := (7740838743994635064744957826602135742894170017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree065.table
  base := (-446211329656066729761297836354058073329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-476588664258090195824398408326218400000000000)
      constant := (7779130457776951169677612030239771128593970871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199997549244860980819/50000000000000000000)
  centralHi := (399995098489721961639/100000000000000000000)
  directionLo := (25194246735001581103/6250000000000000000)
  directionHi := (403107947760025297649/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree066.table
  base := (70523348934310098066880574735911623791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-482728261380561580509725553181868400000000000)
      constant := (7986957558795149810385896578261575443948583982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree066.table
  base := (28200731404215754435723652354226501641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-96784013105572969860316635083710680000000000)
      constant := (1605287313746097281376841178688227624543239841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25194246735001581103/6250000000000000000)
  centralHi := (403107947760025297649/100000000000000000000)
  directionLo := (406196942724580580331/100000000000000000000)
  directionHi := (101549235681145145083/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree067.table
  base := (37625594660932840503364268753059971377/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-98008321002348145982861283381396180000000000)
      constant := (1647397908680395289415754826911766490322067108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree067.table
  base := (150494961958414316328432767086096686387/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-98250293359527900555753588502177680000000000)
      constant := (1655534792900415656815696644204161067297833787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406196942724580580331/100000000000000000000)
  centralHi := (101549235681145145083/25000000000000000000)
  directionLo := (409262623519779910671/100000000000000000000)
  directionHi := (25578913969986244417/6250000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree068.table
  base := (138822808415308250648189552455078387361/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-99470989728583975863777456126418680000000000)
      constant := (1698186927079641876347748658041641909258939122) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree068.table
  base := (173524517388344790803365165328429030611/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-498582868067414156255952709603223400000000000)
      constant := (8532842583992325686710607151428845836330102488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409262623519779910671/100000000000000000000)
  centralHi := (25578913969986244417/6250000000000000000)
  directionLo := (206152755100307852147/50000000000000000000)
  directionHi := (82461102040123140859/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree069.table
  base := (512047520103308924151556217440346644323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-504668292274099028723468144357205900000000000)
      constant := (8748792781838020007498747333215550810724955692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree069.table
  base := (2048162566434024919786552719729016911881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-505914269337188809733137476695558400000000000)
      constant := (8791942375395132719981678290690199776518098081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206152755100307852147/50000000000000000000)
  centralHi := (82461102040123140859/20000000000000000000)
  directionLo := (415326103770623756171/100000000000000000000)
  directionHi := (103831525942655939043/25000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree070.table
  base := (546478695798029731674244818061981083601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-102396327181055635625609801616463680000000000)
      constant := (1802112787561262768925191978292725644033813801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree070.table
  base := (2732369785390478194866523063692691209793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-513245670606963463210322243787893400000000000)
      constant := (9054973294781082390196613527646870143031098393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415326103770623756171/100000000000000000000)
  centralHi := (103831525942655939043/25000000000000000000)
  directionLo := (209162443572444336607/50000000000000000000)
  directionHi := (83664977428977734643/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree071.table
  base := (3440834544473697610927044113598953984759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-519294979536457327532629871807430900000000000)
      constant := (9276248065198172220431931654562875835848526559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree071.table
  base := (8602035360271633920635273479887406829/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4080400000000000000000000000000000000000000
      center := (61206)
      previous := (30603)
      next := (30603)
      square := (291811439703345813279078414315600000000000)
      linear := (-20823082875069524667500280435209136000000000)
      constant := (372877412195898987645600787014309869993002064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209162443572444336607/50000000000000000000)
  centralHi := (83664977428977734643/20000000000000000000)
  directionLo := (84260465210270648443/20000000000000000000)
  directionHi := (52662790756419155277/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree072.table
  base := (4173510107644711087274277157809741846123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-526608323167636476937210735532543400000000000)
      constant := (9545845131684390366781801663730960176572300723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree072.table
  base := (521686568197730328188378650424043791173/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-527908473146512770164691777972563400000000000)
      constant := (9592828374151744190276171010028868965710046184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84260465210270648443/20000000000000000000)
  centralHi := (52662790756419155277/12500000000000000000)
  directionLo := (53032358734399378739/12500000000000000000)
  directionHi := (424258869875195029913/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree073.table
  base := (2465208739758367195208975915240060781769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-533921666798815626341791599257655900000000000)
      constant := (9819355109834617459311524215793374876319651138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree073.table
  base := (2465201181613389379180789872023902454561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-535239874416287423641876545064898400000000000)
      constant := (9867652475750114984934169499867120932877953522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53032358734399378739/12500000000000000000)
  centralHi := (424258869875195029913/100000000000000000000)
  directionLo := (26699684528162806211/6250000000000000000)
  directionHi := (427194952450604899377/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree074.table
  base := (1427888594616051836078797070600852085747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-541235010429994775746372462982768400000000000)
      constant := (10096777976373991158665285893408362543506820588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree074.table
  base := (2855770684665549638129972974112271182373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-542571275686062077119061312157233400000000000)
      constant := (10146407586967693263307634873387329756662773946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26699684528162806211/6250000000000000000)
  centralHi := (427194952450604899377/100000000000000000000)
  directionLo := (43011099280391740877/10000000000000000000)
  directionHi := (430110992803917408771/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree075.table
  base := (814614858554649274114579555593291016091/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-548548354061173925150953326707880900000000000)
      constant := (10378113711552866070195627276523754949491154328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree075.table
  base := (3258453837206021268506004078871309300033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-549902676955836730596246079249568400000000000)
      constant := (10429093688529865373884585719956401827339273266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43011099280391740877/10000000000000000000)
  centralHi := (430110992803917408771/100000000000000000000)
  directionLo := (54125924481462151087/12500000000000000000)
  directionHi := (433007395851697208697/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree076.table
  base := (1469301861313987502628772475913414399953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-111172339538470614911106838086598680000000000)
      constant := (2132672459722473720485945052107721540293920553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree076.table
  base := (3673249837908302492916872577638216684529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-557234078225611384073430846341903400000000000)
      constant := (10715710764087968027402670239136398696797760658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54125924481462151087/12500000000000000000)
  centralHi := (433007395851697208697/100000000000000000000)
  directionLo := (435884553057074181431/100000000000000000000)
  directionHi := (54485569132134272679/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree077.table
  base := (1025040537343771570545572416266659607221/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-563175041323532223960115054158105900000000000)
      constant := (10952523723331159542748389888247493963476091368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree077.table
  base := (256259875442190614441305396850568219489/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-564565479495386037550615613434238400000000000)
      constant := (11006258799774816022176773308278679160024233248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435884553057074181431/100000000000000000000)
  centralHi := (54485569132134272679/12500000000000000000)
  directionLo := (87748568609467865027/20000000000000000000)
  directionHi := (27421427690458707821/6250000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree078.table
  base := (9078362661935729936125546993872795062391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-570488384954711373364695917883218400000000000)
      constant := (11245597973641025720995587655323875257431450591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree078.table
  base := (9078355536337070110286669009163140853251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-571896880765160691027800380526573400000000000)
      constant := (11300737783827886626903427235801334599844013451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87748568609467865027/20000000000000000000)
  centralHi := (27421427690458707821/6250000000000000000)
  directionLo := (110395658048889976843/25000000000000000000)
  directionHi := (441582632195559907373/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree079.table
  base := (9980623392190704360874716498253421872873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-577801728585890522769276781608330900000000000)
      constant := (11542585039300816967537020111219050562775177473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree079.table
  base := (1247577158037751124191810073537417372559/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-579228282034935344504985147618908400000000000)
      constant := (11599147706269831591239996902083386131939794872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110395658048889976843/25000000000000000000)
  centralHi := (441582632195559907373/100000000000000000000)
  directionLo := (444404275168743233061/100000000000000000000)
  directionHi := (222202137584371616531/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree080.table
  base := (5453552818785314742073934789895095406431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-585115072217069672173857645333443400000000000)
      constant := (11843484911619847781090797765427209736482005262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree080.table
  base := (1090710036841252302699268522623744505921/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-117311936660941999596433982942248680000000000)
      constant := (2380297711727514174257499541611330435409800242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444404275168743233061/100000000000000000000)
  centralHi := (222202137584371616531/50000000000000000000)
  directionLo := (223604057722435442723/50000000000000000000)
  directionHi := (447208115444870885447/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree081.table
  base := (185278260548735978788930220100352841993/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-592428415848248821578438509058555900000000000)
      constant := (12148297583223239898087031748525183414084917952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree081.table
  base := (11857804144958870662194146834688934293469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-593891084574484651459354681803578400000000000)
      constant := (12207760333752561393510016398484501493727677269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223604057722435442723/50000000000000000000)
  centralHi := (447208115444870885447/100000000000000000000)
  directionLo := (449994485800937206843/100000000000000000000)
  directionHi := (112498621450234301711/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree082.table
  base := (6416365945675444058787957329329548845737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-599741759479427970983019372783668400000000000)
      constant := (12457023047852830428963039818050798830550726274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree082.table
  base := (12832727997054883280600640655045717002023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-601222485844259304936539448895913400000000000)
      constant := (12517963025525967351829844542604372959137636623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449994485800937206843/100000000000000000000)
  centralHi := (112498621450234301711/25000000000000000000)
  directionLo := (452763708773955059281/100000000000000000000)
  directionHi := (226381854386977529641/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree083.table
  base := (6915937382845923295610211026844488032837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-607055103110607120387600236508780900000000000)
      constant := (12769661300198242578534061783138143401095940474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree083.table
  base := (2766374283687858394695250733823083761939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-121710777422806791682744843197649680000000000)
      constant := (2566419325758683508421793418343537232455539739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452763708773955059281/100000000000000000000)
  centralHi := (226381854386977529641/50000000000000000000)
  directionLo := (455516097096736748897/100000000000000000000)
  directionHi := (227758048548368374449/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree084.table
  base := (7427618428213378032109326837796617461703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-614368446741786269792181100233893400000000000)
      constant := (13086212335753539367186193130906247589453664606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree084.table
  base := (7427616989868029889561471185643390011567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-615885288383808611890908983080583400000000000)
      constant := (13150161139174847011301102304023700643015989934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455516097096736748897/100000000000000000000)
  centralHi := (227758048548368374449/50000000000000000000)
  directionLo := (458251954110116821949/100000000000000000000)
  directionHi := (9165039082202336439/2000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree085.table
  base := (15902817788774454779363900122915247488151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-621681790372965419196761963959005900000000000)
      constant := (13406676150695578163834168218750852345876628351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree085.table
  base := (15902815316799691883212933405076133198153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-623216689653583265368093750172918400000000000)
      constant := (13472156552955607566805292563512926509754358753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458251954110116821949/100000000000000000000)
  centralHi := (9165039082202336439/2000000000000000000)
  directionLo := (460971574153154833913/100000000000000000000)
  directionHi := (230485787076577416957/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree086.table
  base := (4243654311191912532782516094038145325351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-628995134004144568601342827684118400000000000)
      constant := (13731052741780774616609015330976013356855622204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree086.table
  base := (16974615120828545648635160168602655109593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-630548090923357918845278517265253400000000000)
      constant := (13798082866985613652080367879779577484772958193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460971574153154833913/100000000000000000000)
  centralHi := (230485787076577416957/50000000000000000000)
  directionLo := (46367524293273890277/10000000000000000000)
  directionHi := (463675242932738902771/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree087.table
  base := (1129414684666487824316362203326743184473/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-636308477635323718005923691409230900000000000)
      constant := (14059342106257485106283159430173359621846945168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree087.table
  base := (18070633129977478184971348557106686979603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-637879492193132572322463284357588400000000000)
      constant := (14127940078593782964501171438681000288878930203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46367524293273890277/10000000000000000000)
  centralHi := (463675242932738902771/100000000000000000000)
  directionLo := (466363237873903767959/100000000000000000000)
  directionHi := (11659080946847594199/2500000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree088.table
  base := (19190870689655093954761732281226557029401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-643621821266502867410504555134343400000000000)
      constant := (14391544241791640999846949042158689108256919601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree088.table
  base := (9595434561121047428637792119467347887877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-645210893462907225799648051449923400000000000)
      constant := (14461728185515448674396619968119997231608466554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466363237873903767959/100000000000000000000)
  centralHi := (11659080946847594199/2500000000000000000)
  directionLo := (469035828452079193543/100000000000000000000)
  directionHi := (58629478556509899193/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree089.table
  base := (2541915531960081974881309934239996565841/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-650935164897682016815085418859455900000000000)
      constant := (14727659146403627458022125148476483795995152328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree089.table
  base := (20335322909421533136384505085092591701097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-652542294732681879276832818542258400000000000)
      constant := (14799447185830773783106718011018699602942890497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469035828452079193543/100000000000000000000)
  centralHi := (58629478556509899193/12500000000000000000)
  directionLo := (235846638254197495569/50000000000000000000)
  directionHi := (471693276508394991139/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree090.table
  base := (21503995488174249643101920404291059344733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-658248508528861166219666282584568400000000000)
      constant := (15067686818414704255563582535454742471375621333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree090.table
  base := (2150399433199609250250695737269773252267/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-131974739200491306550803517126918680000000000)
      constant := (3028219415582499565125815201649996313892751334) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235846638254197495569/50000000000000000000)
  centralHi := (471693276508394991139/100000000000000000000)
  directionLo := (94867167309817380479/20000000000000000000)
  directionHi := (118583959137271725599/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree091.table
  base := (2837110530950716348231674369391956207869/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-665561852160040315624247146309680900000000000)
      constant := (15411627256401524386375781007237865418461773352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree091.table
  base := (22696883254780914568425353461974799943091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-667205097272231186231202352726928400000000000)
      constant := (15486677860381600061555687348300495109219471291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94867167309817380479/20000000000000000000)
  centralHi := (118583959137271725599/25000000000000000000)
  directionLo := (476963756029972363493/100000000000000000000)
  directionHi := (238481878014986181747/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree092.table
  base := (23913990415696242934857044166268470684487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-672875195791219465028828010034793400000000000)
      constant := (15759480459157525237419459954573002669452451887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree092.table
  base := (4782797912647602979173881902959987574739/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-134907299708401167941677423963852680000000000)
      constant := (3167237906413935702326351373147507753249912539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476963756029972363493/100000000000000000000)
  centralHi := (238481878014986181747/50000000000000000000)
  directionLo := (239788637813448069871/50000000000000000000)
  directionHi := (479577275626896139743/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree093.table
  base := (25155313892205223290101530781305257141417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-680188539422398614433408873759905900000000000)
      constant := (16111246425660152827571703726107778334349594817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree093.table
  base := (25155313160346850130980929535970045531837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-681867899811780493185571886911598400000000000)
      constant := (16189632091987026613104577103214045709470269237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239788637813448069871/50000000000000000000)
  centralHi := (479577275626896139743/100000000000000000000)
  directionLo := (241088314746491198679/50000000000000000000)
  directionHi := (482176629492982397359/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree094.table
  base := (2642085459220275751434766551683551831303/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-137500376610715552767597947497003680000000000)
      constant := (3293385031008607420135667070392424399462243806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree094.table
  base := (26420853963948762737231127448139547338929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-689199301081555146662756654003933400000000000)
      constant := (16547005539295543900444017913955013722404414729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241088314746491198679/50000000000000000000)
  centralHi := (482176629492982397359/100000000000000000000)
  directionLo := (121190511375867864997/25000000000000000000)
  directionHi := (484762045503471459989/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree095.table
  base := (27710612443753915820738829081895743529263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-694815226684756913242570601210130900000000000)
      constant := (16826516646572369837983630458748914885992011863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree095.table
  base := (27710611904493496894100121278824942463149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-696530702351329800139941421096268400000000000)
      constant := (16908309873285748214024955981959138613066582949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121190511375867864997/25000000000000000000)
  centralHi := (484762045503471459989/100000000000000000000)
  directionLo := (487333745488865819427/100000000000000000000)
  directionHi := (121833436372216454857/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree096.table
  base := (14512293692976404187264169564374624500019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-702128570315936062647151464935243400000000000)
      constant := (17190020899626850057283338139838895089049387638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree096.table
  base := (29024586923126875342960228624995489983181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-703862103621104453617126188188603400000000000)
      constant := (17273545093357268091632130319033103793318429381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487333745488865819427/100000000000000000000)
  centralHi := (121833436372216454857/25000000000000000000)
  directionLo := (244945972728530259497/50000000000000000000)
  directionHi := (97978389091412103799/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree097.table
  base := (30362779367253520269994217880689668227927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-709441913947115212051732328660355900000000000)
      constant := (17557437913680657880624188499931880961843083327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree097.table
  base := (30362778970067966382437093299794733103013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-711193504890879107094310955280938400000000000)
      constant := (17642711199002288248979821117714786547383835613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244945972728530259497/50000000000000000000)
  centralHi := (97978389091412103799/20000000000000000000)
  directionLo := (7694325871954491107/1562500000000000000)
  directionHi := (492436855805087430849/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree098.table
  base := (7931297086013269951888859641937267569447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-716755257578294361456313192385468400000000000)
      constant := (17928767688288999393698755484947429640903715388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree098.table
  base := (3965648500403988180974644739815777632661/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-718524906160653760571495722373273400000000000)
      constant := (18015808189791500982643181359122898381046198888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7694325871954491107/1562500000000000000)
  centralHi := (492436855805087430849/100000000000000000000)
  directionLo := (494968681521060868231/100000000000000000000)
  directionHi := (61871085190132608529/12500000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree099.table
  base := (16555907139744197916198026760816117737479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-724068601209473510860894056110580900000000000)
      constant := (18304010223075834203636761612721261590330046558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree099.table
  base := (33111813987061180705554164087162540973269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-725856307430428414048680489465608400000000000)
      constant := (18392836065362184114408817721379965655468317069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494968681521060868231/100000000000000000000)
  centralHi := (61871085190132608529/12500000000000000000)
  directionLo := (99497524475374621187/20000000000000000000)
  directionHi := (31092976398554569121/6250000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree100.table
  base := (17261328571207427275008058161301531918079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-731381944840652660265474919835693400000000000)
      constant := (18683165517723456105120512929825648854192647758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree100.table
  base := (8630664222883457024736149602946298141903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-733187708700203067525865256557943400000000000)
      constant := (18773794825408083588933685604354625749382210012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99497524475374621187/20000000000000000000)
  centralHi := (31092976398554569121/6250000000000000000)
  directionLo := (31249617069509528253/6250000000000000000)
  directionHi := (499993873112152452049/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree101.table
  base := (7191543381307829900003808957622140846207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (143030800756467901813095978000000000000)
      linear := (-14482801460088850302324395325180000000000)
      constant := (373811068953311382784972138053453390846207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree101.table
  base := (17978858345660880924382016391684495546269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (715154003782339509065479890000000000000)
      linear := (-72592795801389836388888346598400000000000)
      constant := (1878118269745204156767387573464043991092538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31249617069509528253/6250000000000000000)
  centralHi := (499993873112152452049/100000000000000000000)
  directionLo := (50248762360996327211/10000000000000000000)
  directionHi := (502487623609963272111/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree102.table
  base := (37416993549683062483081870399679108575947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-746008632103010959074636647285918400000000000)
      constant := (19453214385570167121266440925636511461583235347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree102.table
  base := (374169933650765216640113124611280227163/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4080400000000000000000000000000000000000000
      center := (61206)
      previous := (30603)
      next := (30603)
      square := (291811439703345813279078414315600000000000)
      linear := (-29914020449590094979209391629704536000000000)
      constant := (781900199917305620549264801581018782389159052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50248762360996327211/10000000000000000000)
  centralHi := (502487623609963272111/100000000000000000000)
  directionLo := (504969059064696587553/100000000000000000000)
  directionHi := (252484529532348293777/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree103.table
  base := (38900487053158430308209746179208221773039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-753321975734190108479217511011030900000000000)
      constant := (19844107958352378279365985568462413976556770839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree103.table
  base := (1945024344741157905840374174908067283499/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-151036382501905405591483911566989680000000000)
      constant := (3988051282002031972292478120599711932435893196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504969059064696587553/100000000000000000000)
  centralHi := (252484529532348293777/50000000000000000000)
  directionLo := (63429795017821418611/12500000000000000000)
  directionHi := (507438360142571348889/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree104.table
  base := (40408197401236517318073900047595447486317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-760635319365369257883798374736143400000000000)
      constant := (20238914290149831720805727025915172159807919717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree104.table
  base := (8081639453089179249223725265241798451001/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-152502662755860336286920864985456680000000000)
      constant := (4067387741149837925199785062762032625998661201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63429795017821418611/12500000000000000000)
  centralHi := (507438360142571348889/100000000000000000000)
  directionLo := (254947851567570017351/50000000000000000000)
  directionHi := (509895703135140034703/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree105.table
  base := (41940124580697547371232377601360055297131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-767948662996548407288379238461255900000000000)
      constant := (20637633380827672509166815921124879080336033331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree105.table
  base := (20970062232125846848611963436980668725743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-769844715049076334911789092019618400000000000)
      constant := (20737551885020248082280717147618850478342608686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254947851567570017351/50000000000000000000)
  centralHi := (509895703135140034703/100000000000000000000)
  directionLo := (128085315026541920289/25000000000000000000)
  directionHi := (512341260106167681157/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree106.table
  base := (10874067145112074919562985473330344644981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-775262006627727556692960102186368400000000000)
      constant := (21040265230272738699176243803993344757893804724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree106.table
  base := (5437033560074988842430398827349048832853/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-777176116318850988388973859111953400000000000)
      constant := (21142095947714790064415097440099313977151467624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128085315026541920289/25000000000000000000)
  centralHi := (512341260106167681157/100000000000000000000)
  directionLo := (514775199032230649623/100000000000000000000)
  directionHi := (64346899879028831203/12500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree107.table
  base := (45076629391197498592177328311345370244627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-782575350258906706097540965911480900000000000)
      constant := (21446809838390249987959420020212189778115440027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree107.table
  base := (45076629305588092274801550966542586130733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-784507517588625641866158626204288400000000000)
      constant := (21550570893742001627947624577124531896119607333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514775199032230649623/100000000000000000000)
  centralHi := (64346899879028831203/12500000000000000000)
  directionLo := (517197683937360252383/100000000000000000000)
  directionHi := (16162427623042507887/3125000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree108.table
  base := (46681207005180277331893877682519934575851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-789888693890085855502121829636593400000000000)
      constant := (21857267205100996969482193931558537852608256051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree108.table
  base := (5835150866473171842092133635514637183497/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-791838918858400295343343393296623400000000000)
      constant := (21962976723026080533635800220658103911270823176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517197683937360252383/100000000000000000000)
  centralHi := (16162427623042507887/3125000000000000000)
  directionLo := (103921775004407330087/20000000000000000000)
  directionHi := (129902218755509162609/25000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree109.table
  base := (24155000707962155699721718460558037772411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-797202037521265004906702693361705900000000000)
      constant := (22271637330338955461540894418404867492882729222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree109.table
  base := (48310001353006314523248643939630939845419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-799170320128174948820528160388958400000000000)
      constant := (22379313435503929071295611139073771292363119219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103921775004407330087/20000000000000000000)
  centralHi := (129902218755509162609/25000000000000000000)
  directionLo := (130502232196705024251/25000000000000000000)
  directionHi := (104401785757364019401/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree110.table
  base := (49963012618051334543633862934750956909563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-804515381152444154311283557086818400000000000)
      constant := (22689920214049261770107110429065781386434452163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree110.table
  base := (24981506282059512017546050929738618471729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-806501721397949602297712927481293400000000000)
      constant := (22799581031123196855527167516727070294060215058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130502232196705024251/25000000000000000000)
  centralHi := (104401785757364019401/20000000000000000000)
  directionLo := (524397998150889519029/100000000000000000000)
  directionHi := (52439799815088951903/10000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree111.table
  base := (5164024060710869856252893955251986940019/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-162365744956724660743172884162386180000000000)
      constant := (4622423171237298886174578124476376118800267638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree111.table
  base := (25820120280441212972869361829637348105571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-813833122667724255774897694573628400000000000)
      constant := (23223779509840620656522549889218127351049859542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524397998150889519029/100000000000000000000)
  centralHi := (52439799815088951903/10000000000000000000)
  directionLo := (263388116282871254889/50000000000000000000)
  directionHi := (526776232565742509779/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree112.table
  base := (53341685379426443517341104398407503760587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-819142068414802453120445284537043400000000000)
      constant := (23538224256713216182502663074555432945861747987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree112.table
  base := (53341685339808220994396131480556515489529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-821164523937498909252082461665963400000000000)
      constant := (23651908871620616333522415210012722614508685329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263388116282871254889/50000000000000000000)
  centralHi := (526776232565742509779/100000000000000000000)
  directionLo := (529143778124295959819/100000000000000000000)
  directionHi := (26457188906214797991/5000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree113.table
  base := (55067346931996028681679195381918644574727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-826455412045981602525026148262155900000000000)
      constant := (23968245415598736901046511541101296749556790127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree113.table
  base := (11013469379608766110952831307602549815403/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-165699185041454712545853445751659680000000000)
      constant := (4816793823286816946391975091466381865666926003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529143778124295959819/100000000000000000000)
  centralHi := (26457188906214797991/5000000000000000000)
  directionLo := (132875194416403174933/25000000000000000000)
  directionHi := (531500777665612699733/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree114.table
  base := (56817225262367455131342401793924310910723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-833768755677160751929607011987268400000000000)
      constant := (24402179332818064147478663551975647270600285323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree114.table
  base := (56817225233273140464733974735869823532841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-835827326477048216206451995850633400000000000)
      constant := (24519960244257399171267258516574701269858511041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132875194416403174933/25000000000000000000)
  centralHi := (531500777665612699733/100000000000000000000)
  directionLo := (533847370875466591623/100000000000000000000)
  directionHi := (66730921359433323953/12500000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree115.table
  base := (58591320368562003872089440699952926749633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-841082099308339901334187875712380900000000000)
      constant := (24840026008351013009338863779963939962023006233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree115.table
  base := (58591320343632352354845950198051807716603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-843158727746822869683636762942968400000000000)
      constant := (24959882255071547044277706642169247865517067203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533847370875466591623/100000000000000000000)
  centralHi := (66730921359433323953/12500000000000000000)
  directionLo := (536183694382946419487/100000000000000000000)
  directionHi := (16755740449467075609/3125000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree116.table
  base := (30194816124499116015506441245976145723479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-848395442939519050738768739437493400000000000)
      constant := (25281785442181451187880583535634434325050418558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree116.table
  base := (60389632227638655923472963852786880337493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-850490129016597523160821530035303400000000000)
      constant := (25403735148861402203104321592464404766322766093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536183694382946419487/100000000000000000000)
  centralHi := (16755740449467075609/3125000000000000000)
  directionLo := (16828433807915238377/3125000000000000000)
  directionHi := (107701976370657525613/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree117.table
  base := (62212160902429225127000607719856477782389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-855708786570698200143349603162605900000000000)
      constant := (25727457634296658908481998088477007836108150189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree117.table
  base := (3888260055258111328213100240292712669099/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-857821530286372176638006297127638400000000000)
      constant := (25851518925615108332301288961123321865999662384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16828433807915238377/3125000000000000000)
  centralHi := (107701976370657525613/20000000000000000000)
  directionLo := (540826064077110388567/100000000000000000000)
  directionHi := (67603258009638798571/12500000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree118.table
  base := (8007363290986175664553446816891908353647/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-863022130201877349547930466887718400000000000)
      constant := (26177042584686786311560288386594803731924424376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree118.table
  base := (64058906312212783641948954331933612801219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-865152931556146830115191064219973400000000000)
      constant := (26303233585323556503017501499643718184185235019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540826064077110388567/100000000000000000000)
  centralHi := (67603258009638798571/12500000000000000000)
  directionLo := (543132369056232574637/100000000000000000000)
  directionHi := (271566184528116287319/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree119.table
  base := (65929868524649451871119334225769762617041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-870335473833056498952511330612830900000000000)
      constant := (26630540293344393596367346878676517254706435241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree119.table
  base := (6592986851122066251814975103197021064243/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-174496866565184296718475166262461680000000000)
      constant := (5351775825595988528473516274215824938752685686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543132369056232574637/100000000000000000000)
  centralHi := (271566184528116287319/50000000000000000000)
  directionLo := (545428922086216964507/100000000000000000000)
  directionHi := (136357230521554241127/25000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree120.table
  base := (33912523746089053927154292604293929805887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-877648817464235648357092194337943400000000000)
      constant := (27087950760264061410891210321272209755899706574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree120.table
  base := (8478130935084453414214473525098425904107/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-879815734095696137069560598404643400000000000)
      constant := (27218455553579392808784740980634938341182364056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545428922086216964507/100000000000000000000)
  centralHi := (136357230521554241127/25000000000000000000)
  directionLo := (547715845835803300883/100000000000000000000)
  directionHi := (136928961458950825221/25000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree121.table
  base := (69744443230109831847247698577153242073441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-884962161095414797761673058063055900000000000)
      constant := (27549273985442060867119234151907324378641171641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree121.table
  base := (69744443220258002749381242766010604381551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-887147135365470790546745365496978400000000000)
      constant := (27681962862118645994745189667149865850296201751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547715845835803300883/100000000000000000000)
  centralHi := (136928961458950825221/25000000000000000000)
  directionLo := (137498315105841924313/25000000000000000000)
  directionHi := (549993260423367697253/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree122.table
  base := (14337611147643482118914154848837749238967/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-178455100945318789433250784357633680000000000)
      constant := (5602901993775214832526686164758309354986702367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree122.table
  base := (35844027864889959111611257880802948362557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-894478536635245444023930132589313400000000000)
      constant := (28149401053595785732238704797571395352492887914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137498315105841924313/25000000000000000000)
  centralHi := (549993260423367697253/100000000000000000000)
  directionLo := (552261283490544240259/100000000000000000000)
  directionHi := (27613064174527212013/5000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree123.table
  base := (73655885016388781783451314031176408709777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-899588848357773096570834785513280900000000000)
      constant := (28483658710564958149780657229005815201498435177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree123.table
  base := (7365588500916305536035979139998858044437/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-180361987581004019500222979936329680000000000)
      constant := (5724154025602002619104627474210075056822603674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552261283490544240259/100000000000000000000)
  centralHi := (27613064174527212013/5000000000000000000)
  directionLo := (17328750946035514607/3125000000000000000)
  directionHi := (22180801210925458697/4000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree124.table
  base := (15129586212921485883765393520973699715451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-181380438397790449195083129847678680000000000)
      constant := (5791344042101708869779056466360133910797315651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree124.table
  base := (75647931058419837544391730015502605819779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-909141339174794750978299666773983400000000000)
      constant := (29096070085361454815534577321657448281967565579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17328750946035514607/3125000000000000000)
  centralHi := (22180801210925458697/4000000000000000000)
  directionLo := (278384806834719832723/50000000000000000000)
  directionHi := (556769613669439665447/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree125.table
  base := (7766419388293581043475278300689538947579/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-182843107124026279075999302592701180000000000)
      constant := (5886738893741493976632320335449756254858506758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree125.table
  base := (15532838775527507688543383234718828474083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-183294548088913880891096886773263680000000000)
      constant := (5915060185130200234190831522108946144264120683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278384806834719832723/50000000000000000000)
  centralHi := (556769613669439665447/100000000000000000000)
  directionLo := (559010144306088606807/100000000000000000000)
  directionHi := (69876268038261075851/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree126.table
  base := (39852336735750676431728481213545370149349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-921528879251310544784577376688618400000000000)
      constant := (29914581485163034645936375155888643516787018298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree126.table
  base := (9963084183370608205895805031612026250359/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-923804141714344057932669200958653400000000000)
      constant := (30058462648880169127926147190664658038239297272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (559010144306088606807/100000000000000000000)
  centralHi := (69876268038261075851/12500000000000000000)
  directionLo := (11224834612030787877/2000000000000000000)
  directionHi := (561241730601539393851/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree127.table
  base := (81769369830484635253958087268065840458599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-928842222882489694189158240413730900000000000)
      constant := (30399381259877080718998141316608294044768168399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree127.table
  base := (20442342456650160676915586057372915034747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-931135542984118711409853968050988400000000000)
      constant := (30545555255050986885483300812215251400077816588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11224834612030787877/2000000000000000000)
  centralHi := (561241730601539393851/100000000000000000000)
  directionLo := (281732239413644242131/50000000000000000000)
  directionHi := (563464478827288484263/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree128.table
  base := (262057134250341924833410104057540399501/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-187231113302733768718747820827768680000000000)
      constant := (6177618758570378132235535673464628455379820864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree128.table
  base := (83858282956784269845861202441277345426839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-938466944253893364887038735143323400000000000)
      constant := (31036578744165896565286737190017396600699184639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281732239413644242131/50000000000000000000)
  centralHi := (563464478827288484263/100000000000000000000)
  directionLo := (565678493166926706549/100000000000000000000)
  directionHi := (11313569863338534131/2000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree129.table
  base := (42985706430317115422614141318174241592709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-943468910144847992998319967863955900000000000)
      constant := (31380719084090101797227323077521114533224449018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree129.table
  base := (85971412857787692030909380932806565101217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-945798345523668018364223502235658400000000000)
      constant := (31531533116227672277966718404091581845597514617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (565678493166926706549/100000000000000000000)
  centralHi := (11313569863338534131/2000000000000000000)
  directionLo := (567883875773121116621/100000000000000000000)
  directionHi := (283941937886560558311/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree130.table
  base := (5506797470771582551190341643099170813433/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-950782253776027142402900831589068400000000000)
      constant := (31877257133594634070256602479711903638485280528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree130.table
  base := (3524350381196345767272741917656355454651/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4080400000000000000000000000000000000000000
      center := (61206)
      previous := (30603)
      next := (30603)
      square := (291811439703345813279078414315600000000000)
      linear := (-38125189871737706873656330773119736000000000)
      constant := (1281216734849574048697283299285072241992894851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567883875773121116621/100000000000000000000)
  centralHi := (283941937886560558311/50000000000000000000)
  directionLo := (570080726822612876839/100000000000000000000)
  directionHi := (14252018170565321921/2500000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree131.table
  base := (18054064595110137191768864922230442345803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-191619119481441258361496339062836180000000000)
      constant := (6475541588273725877838152597407342573619536403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree131.table
  base := (90270322973464978135218562020718361016873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-960461148063217325318593036420328400000000000)
      constant := (32533234509204175790268290611228690175733121473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (570080726822612876839/100000000000000000000)
  centralHi := (14252018170565321921/2500000000000000000)
  directionLo := (286134572284657469017/50000000000000000000)
  directionHi := (114453828913862987607/20000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree132.table
  base := (46228051595287547276665392753499249821577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-965408941038385441212062559039293400000000000)
      constant := (32882071507415400715342893770064174694859813954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree132.table
  base := (23114025797197476405276271943379759728933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-967792549332991978795777803512663400000000000)
      constant := (33039981530125545089333028566010234315979382132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286134572284657469017/50000000000000000000)
  centralHi := (114453828913862987607/20000000000000000000)
  directionLo := (114889845079117831127/20000000000000000000)
  directionHi := (143612306348897288909/25000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree133.table
  base := (94666100177755900683299263008023782017953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-972722284669564590616643422764405900000000000)
      constant := (33390347831738389397691178646323481506615138553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree133.table
  base := (94666100176228016618742519682481787745983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-975123950602766632272962570604998400000000000)
      constant := (33550659434006974277004772434589163991796772583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114889845079117831127/20000000000000000000)
  centralHi := (143612306348897288909/25000000000000000000)
  directionLo := (57662106386177855701/10000000000000000000)
  directionHi := (576621063861778557011/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree134.table
  base := (96900313937439546431526016295421679732251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-980035628300743740021224286489518400000000000)
      constant := (33902536914341129491922018235721989429948692451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree134.table
  base := (96900313936131953795921694198386737621357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-982455351872541285750147337697333400000000000)
      constant := (34065268220852060661137656539599887310475462757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57662106386177855701/10000000000000000000)
  centralHi := (576621063861778557011/100000000000000000000)
  directionLo := (289392376377033391711/50000000000000000000)
  directionHi := (578784752754066783423/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree135.table
  base := (24789686117494660869154368727722424432643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-987348971931922889425805150214630900000000000)
      constant := (34418638755227217989768876726014554712799564972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree135.table
  base := (99158744468859641841035956368626617005451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-989786753142315939227332104789668400000000000)
      constant := (34583807890664455431477981393870857495072605651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289392376377033391711/50000000000000000000)
  centralHi := (578784752754066783423/100000000000000000000)
  directionLo := (580940383130733242629/100000000000000000000)
  directionHi := (58094038313073324263/10000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree136.table
  base := (101441391775729544777765444536043445651877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-994662315563102038830386013939743400000000000)
      constant := (34938653354400290047768469726959338189094797277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree136.table
  base := (101441391774771985866001116321773018446137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-997118154412090592704516871882003400000000000)
      constant := (35106278443447840181072400176523633361169043537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580940383130733242629/100000000000000000000)
  centralHi := (58094038313073324263/10000000000000000000)
  directionLo := (145772011091717303553/25000000000000000000)
  directionHi := (583088044366869214213/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree137.table
  base := (25937063963762582647963186726546133385061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1001975659194281188234966877664855900000000000)
      constant := (35462580711863998442621258903078151582894029044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree137.table
  base := (51874127927115483051207083258511411210057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1004449555681865246181701638974338400000000000)
      constant := (35632679879205907470263433807634482286507582914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145772011091717303553/25000000000000000000)
  centralHi := (583088044366869214213/100000000000000000000)
  directionLo := (18288369506175532409/3125000000000000000)
  directionHi := (585227824197617037089/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree138.table
  base := (106079336708299144556793857438382729177561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1009289002825460337639547741389968400000000000)
      constant := (35990420827621996597577609818100523595340299761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree138.table
  base := (26519834176899516796145673563477341925081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1011780956951639899658886406066673400000000000)
      constant := (36163012197942344803805653985245943859911005124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18288369506175532409/3125000000000000000)
  centralHi := (585227824197617037089/100000000000000000000)
  directionLo := (587359808759991566131/100000000000000000000)
  directionHi := (146839952189997891533/25000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree139.table
  base := (108434634335832825333075854125916742165791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1016602346456639487044128605115080900000000000)
      constant := (36522173701677924623813151154635890343083233991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree139.table
  base := (108434634335232989709206599641759204268287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1019112358221414553136071173159008400000000000)
      constant := (36697275399660821487485996390373258217740795687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (587359808759991566131/100000000000000000000)
  centralHi := (146839952189997891533/25000000000000000000)
  directionLo := (294742041316670150973/50000000000000000000)
  directionHi := (589484082633340301947/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree140.table
  base := (110814148738005787580525710488633248305253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1023915690087818636448709468840193400000000000)
      constant := (37057839334035397905272777869560207765961885853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree140.table
  base := (110814148737492599735593517074692385640243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1026443759491189206613255940251343400000000000)
      constant := (37235469484364977911975458201470844025916118843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294742041316670150973/50000000000000000000)
  centralHi := (589484082633340301947/100000000000000000000)
  directionLo := (73950091109811995603/12500000000000000000)
  directionHi := (23664029155139838593/4000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree141.table
  base := (113217879915169113081344250373882675792247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1031229033718997785853290332565305900000000000)
      constant := (37597417724697997827216720566940297582006711647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree141.table
  base := (14152234989341259832145883838929406837139/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1033775160760963860090440707343678400000000000)
      constant := (37777594452058416880668353808581868708165239512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73950091109811995603/12500000000000000000)
  centralHi := (23664029155139838593/4000000000000000000)
  directionLo := (593709829075672791753/100000000000000000000)
  directionHi := (296854914537836395877/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree142.table
  base := (115645827867669818791952661668230542758577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1038542377350176935257871196290418400000000000)
      constant := (38140908873669264309617431784407014641680243977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree142.table
  base := (57822913933647120808535718935151318183723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1041106562030738513567625474436013400000000000)
      constant := (38323650302744696656839896964530461793584316646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593709829075672791753/100000000000000000000)
  centralHi := (296854914537836395877/50000000000000000000)
  directionLo := (595811463361155475491/100000000000000000000)
  directionHi := (148952865840288868873/25000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree143.table
  base := (59048996297925136837666653007242540540313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1045855720981356084662452060015530900000000000)
      constant := (38688312780952689858266294593078645718353465826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree143.table
  base := (118097992595528997512735039786021659925239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1048437963300513167044810241528348400000000000)
      constant := (38873637036427325455152754994332074727897363039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595811463361155475491/100000000000000000000)
  centralHi := (148952865840288868873/25000000000000000000)
  directionLo := (298952855231413714643/50000000000000000000)
  directionHi := (597905710462827429287/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree144.table
  base := (30143593525011935117082611180254903525151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1053169064612535234067032923740643400000000000)
      constant := (39239629446551714890341857302561907083440261404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree144.table
  base := (12057437409977292776779704446984777024763/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-211153872914057564104399001724136680000000000)
      constant := (7885510930621951428941894210173904860859214726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298952855231413714643/50000000000000000000)
  centralHi := (597905710462827429287/100000000000000000000)
  directionLo := (599992647734582942457/100000000000000000000)
  directionHi := (299996323867291471229/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree145.table
  base := (6153748619029701109516928376283085919591/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-212096481648742876694322757493151180000000000)
      constant := (7958971774093944825688992620534475569112991164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree145.table
  base := (123074972380358964556438198312307845029937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1063100765840062473999179775713018400000000000)
      constant := (39985403152795387966618862928072575202150387337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599992647734582942457/100000000000000000000)
  centralHi := (299996323867291471229/50000000000000000000)
  directionLo := (37629521949354111489/6250000000000000000)
  directionHi := (24082894047586631353/4000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree146.table
  base := (7849986714863449768692146939190950314079/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1067795751874893532876194651190868400000000000)
      constant := (40354001052710043888721779811392823521462718064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree146.table
  base := (62799893718807076069826858393068256653429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1070432167109837127476364542805353400000000000)
      constant := (40547182535487554099387342818978593372243258458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37629521949354111489/6250000000000000000)
  centralHi := (24082894047586631353/4000000000000000000)
  directionLo := (302072447766487452717/50000000000000000000)
  directionHi := (120828979106594981087/20000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree147.table
  base := (128148819272031422029049918334237282589123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1075109095506072682280775514915980900000000000)
      constant := (40917055993275940115523565596558532675941643723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree147.table
  base := (25629763854371895499162524748900943214933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-215552713675922356190709861979537680000000000)
      constant := (8222578560237905986236250627182755116735531533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302072447766487452717/50000000000000000000)
  centralHi := (120828979106594981087/20000000000000000000)
  directionLo := (24248414167695043687/4000000000000000000)
  directionHi := (37888147137023505761/6250000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree148.table
  base := (130722067883556808679732069877105914119773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1082422439137251831685356378641093400000000000)
      constant := (41484023692170617037814181289354894429935804373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree148.table
  base := (65361033941704879283634037016646327654531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1085094969649386434430734076990023400000000000)
      constant := (41682533949904526919830538411460945776807741462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24248414167695043687/4000000000000000000)
  centralHi := (37888147137023505761/6250000000000000000)
  directionLo := (608268799349056688061/100000000000000000000)
  directionHi := (304134399674528344031/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree149.table
  base := (133319533272699334513312380492406808982909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1089735782768430981089937242366205900000000000)
      constant := (42054904149397216341846243144691551764684654709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree149.table
  base := (133319533272573580258805010413477867946029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1092426370919161087907918844082358400000000000)
      constant := (42256105981635692939948909846724835805917441829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (608268799349056688061/100000000000000000000)
  centralHi := (304134399674528344031/50000000000000000000)
  directionLo := (610320301966958901891/100000000000000000000)
  directionHi := (152580075491739725473/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree150.table
  base := (27188243087952161505519225833395154415831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-219409825279922026098903621218263680000000000)
      constant := (8525939472991763354201072562702643345195892031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree150.table
  base := (531020372811145585396740087128768243801/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1099757772188935741385103611174693400000000000)
      constant := (42833608896386112032233307283817889602883584256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (610320301966958901891/100000000000000000000)
  centralHi := (152580075491739725473/25000000000000000000)
  directionLo := (612364931821325648743/100000000000000000000)
  directionHi := (76545616477665706093/12500000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree151.table
  base := (138587114385036860731119408502827909509841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1104362470030789279899098969816430900000000000)
      constant := (43208403338858434077611616976453045411159888041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree151.table
  base := (138587114384944904879572733527117281949977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1107089173458710394862288378267028400000000000)
      constant := (43415042694158804483302272445001441568171715377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (612364931821325648743/100000000000000000000)
  centralHi := (76545616477665706093/12500000000000000000)
  directionLo := (614402757526391414701/100000000000000000000)
  directionHi := (307201378763195707351/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree152.table
  base := (141257230108816975702063523446439449024243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1111675813661968429303679833541543400000000000)
      constant := (43791022071099021263244033125270041819496302843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree152.table
  base := (5650289204349533893622618471366473144747/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4080400000000000000000000000000000000000000
      center := (61206)
      previous := (30603)
      next := (30603)
      square := (291811439703345813279078414315600000000000)
      linear := (-44576822989139401933578925814374536000000000)
      constant := (1760016294998269087028030686939852096549564147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (614402757526391414701/100000000000000000000)
  centralHi := (307201378763195707351/50000000000000000000)
  directionLo := (123286769312449847203/20000000000000000000)
  directionHi := (38527115410140577251/6250000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree153.table
  base := (28790312522276905838228532153132324247467/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-223797831458629515741652139453331180000000000)
      constant := (8875510712336693810827329335836611270898410867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree153.table
  base := (143951562611317299608672756843119576869301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1121751975998259701816657912451698400000000000)
      constant := (44589702938782774157245272518035856078643739501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123286769312449847203/20000000000000000000)
  centralHi := (38527115410140577251/6250000000000000000)
  directionLo := (618458265300923556441/100000000000000000000)
  directionHi := (309229132650461778221/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree154.table
  base := (29334022378603371671593651010659994617737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-225260500184865345622568312198353680000000000)
      constant := (8993599562122921313330930776494659680095535137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree154.table
  base := (146670111892959377509083190495046981906253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1129083377268034355293842679544033400000000000)
      constant := (45182929385639777386968537099460669462425686853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618458265300923556441/100000000000000000000)
  centralHi := (309229132650461778221/50000000000000000000)
  directionLo := (31023803951583873203/5000000000000000000)
  directionHi := (620476079031677464061/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree155.table
  base := (74706438976992670466504843172727107421817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1133615844555505877517422424716880900000000000)
      constant := (45562354817895202125026572880889021101869910434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree155.table
  base := (149412877953936197245990265062260009496939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1136414778537809008771027446636368400000000000)
      constant := (45780086715530507621769538834960687731878274739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31023803951583873203/5000000000000000000)
  centralHi := (620476079031677464061/100000000000000000000)
  directionLo := (155621837996395401953/25000000000000000000)
  directionHi := (622487351985581607813/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree156.table
  base := (152179860794555487192342167170183529560887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1140929188186685026922003288441993400000000000)
      constant := (46160624583527964199578646917428956185050608287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree156.table
  base := (6087194431780538926526465916640590094717/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4080400000000000000000000000000000000000000
      center := (61206)
      previous := (30603)
      next := (30603)
      square := (291811439703345813279078414315600000000000)
      linear := (-45749847192303346489928488549148136000000000)
      constant := (1855246997138307016546762067975603771556208117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155621837996395401953/25000000000000000000)
  centralHi := (622487351985581607813/100000000000000000000)
  directionLo := (312246073679685475449/50000000000000000000)
  directionHi := (624492147359370950899/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree157.table
  base := (154971060414987041136175385731816076962467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1148242531817864176326584152167105900000000000)
      constant := (46762807107515542438857015021465455207344125867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree157.table
  base := (77485530207475561938560058423749434454377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1151077581077358315725396980821038400000000000)
      constant := (46986194024423932192474224548996794436738199554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312246073679685475449/50000000000000000000)
  centralHi := (624492147359370950899/100000000000000000000)
  directionLo := (313245263669307215029/50000000000000000000)
  directionHi := (626490527338614430059/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree158.table
  base := (39446619203883522172128165000602137600073/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1155555875449043325731165015892218400000000000)
      constant := (47368902389860528773372435039631468497633378692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree158.table
  base := (157786476815503384719417285492127713343451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1158408982347132969202581747913373400000000000)
      constant := (47595144003431871412802215394475660203816543651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313245263669307215029/50000000000000000000)
  centralHi := (626490527338614430059/100000000000000000000)
  directionLo := (314241276560110776711/50000000000000000000)
  directionHi := (628482553120221553423/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree159.table
  base := (160626109996445171095937336858436275684907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1162869219080222475135745879617330900000000000)
      constant := (47978910430565458572381303693413920854511736307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree159.table
  base := (40156527499104731192023922192475671491799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1165740383616907622679766515005708400000000000)
      constant := (48208024865484029747918136134545625874551366396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314241276560110776711/50000000000000000000)
  centralHi := (628482553120221553423/100000000000000000000)
  directionLo := (78808535616788622813/12500000000000000000)
  directionHi := (126093656986861796501/20000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree160.table
  base := (8174497997898170100421364635103620450283/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-234036512542280324908065348668488680000000000)
      constant := (9718566245926562367645409059998276128853347532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree160.table
  base := (163489959957940967038734933071876536618647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1173071784886682276156951282098043400000000000)
      constant := (48824836610582888315803914334001820550046818047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78808535616788622813/12500000000000000000)
  centralHi := (126093656986861796501/20000000000000000000)
  directionLo := (632447782065449203193/100000000000000000000)
  directionHi := (316223891032724601597/50000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree161.table
  base := (166378026700326586982722178555827794589351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1177495906342580773944907607067555900000000000)
      constant := (49210664787065014425393961039444480988855969551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree161.table
  base := (1299828333596151645707661576804211063457/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1180403186156456929634136049190378400000000000)
      constant := (49445579238730873925374975005523152578465581696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (632447782065449203193/100000000000000000000)
  centralHi := (316223891032724601597/50000000000000000000)
  directionLo := (158605275718330623501/25000000000000000000)
  directionHi := (126884220574664498801/20000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree162.table
  base := (1354322481790138754930370903171884311153/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4080400000000000000000000000000000000000000
      center := (61206)
      previous := (30603)
      next := (30603)
      square := (291811439703345813279078414315600000000000)
      linear := (-47392369998950396933979538831706736000000000)
      constant := (1993296444114577570945785477784195454290358765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree162.table
  base := (169290310223750953990049820736957558396607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1187734587426231583111320816282713400000000000)
      constant := (50070252749930360332871156800031959653203788007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158605275718330623501/25000000000000000000)
  centralHi := (126884220574664498801/20000000000000000000)
  directionLo := (159097076203198136217/25000000000000000000)
  directionHi := (636388304812792544869/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree163.table
  base := (172226810528513226703523472450973853565857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1192122593604939072754069334517780900000000000)
      constant := (50458070177033407646484228381713991436475307257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree163.table
  base := (172226810528499218068237048237724055996831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1195065988696006236588505583375048400000000000)
      constant := (50698857144183669500226636736394166870223673031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159097076203198136217/25000000000000000000)
  centralHi := (636388304812792544869/100000000000000000000)
  directionLo := (12766988889068505287/2000000000000000000)
  directionHi := (638349444453425264351/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree164.table
  base := (35037505522957368392066871756333649671629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (306030)
      previous := (153015)
      next := (153015)
      square := (1459057198516729066395392071578000000000000)
      linear := (-239887187447223644431730039648578680000000000)
      constant := (10217528401914838073554639193511917760300287429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree164.table
  base := (175187527614774869415877485709732673426813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1202397389965780890065690350467383400000000000)
      constant := (51331392421493072848721443787771391201626919413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12766988889068505287/2000000000000000000)
  centralHi := (638349444453425264351/100000000000000000000)
  directionLo := (128060915499693907047/20000000000000000000)
  directionHi := (160076144374617383809/25000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree165.table
  base := (89086230741402986996982603652530461349951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1206749280867297371563231061968005900000000000)
      constant := (51721126600489009050639206029575315378711700302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree165.table
  base := (5567889421337366936961107038735533426033/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1209728791235555543542875117559718400000000000)
      constant := (51967858581860792502477327517738566522326804256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128060915499693907047/20000000000000000000)
  centralHi := (160076144374617383809/25000000000000000000)
  directionLo := (642253758803317935963/100000000000000000000)
  directionHi := (160563439700829483991/25000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree166.table
  base := (90590806066391850901998738810966765265669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1214062624498476520967811925693118400000000000)
      constant := (52358523949780037313956989037148744819950178938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree166.table
  base := (181181612132774957612361491813527021963281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1217060192505330197020059884652053400000000000)
      constant := (52608255625289002517419735791781854951047429481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642253758803317935963/100000000000000000000)
  centralHi := (160563439700829483991/25000000000000000000)
  directionLo := (64419704239346473671/10000000000000000000)
  directionHi := (644197042393464736711/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree167.table
  base := (92107489782464258596486566948511750299509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1221375968129655670372392789418230900000000000)
      constant := (52999834057449401982604275566724363635860582618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree167.table
  base := (92107489782460522374859085896447743572847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1224391593775104850497244651744388400000000000)
      constant := (53252583551779830092216342993271785839373224494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64419704239346473671/10000000000000000000)
  centralHi := (644197042393464736711/100000000000000000000)
  directionLo := (646134481481977802103/100000000000000000000)
  directionHi := (80766810185247225263/12500000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree168.table
  base := (187272563779444440542114630593376150357611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1228689311760834819776973653143343400000000000)
      constant := (53645056923499184268489915876279697109797989811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree168.table
  base := (187272563779438055113286052531778612296037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1231722995044879503974429418836723400000000000)
      constant := (53900842361335356758447165573807902024031873437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell070.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (646134481481977802103/100000000000000000000)
  centralHi := (80766810185247225263/12500000000000000000)
  directionLo := (648066128486500386187/100000000000000000000)
  directionHi := (162016532121625096547/25000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree169.table
  base := (190354364776531134472369533616578398247861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1236002655392013969181554516868455900000000000)
      constant := (54294192547931420930010196085617637396776430061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree169.table
  base := (190354364776525678122908982266162200146791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1530150)
      previous := (765075)
      next := (765075)
      square := (7295285992583645331976960357890000000000000)
      linear := (-1239054396314654157451614185929058400000000000)
      constant := (54553032053957619547884030629245494678697414991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell070.Kernel169
