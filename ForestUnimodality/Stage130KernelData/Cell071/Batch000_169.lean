import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell071.Parameters
import ForestUnimodality.BinomialMassData.Q405_808.Batch000_049
import ForestUnimodality.BinomialMassData.Q405_808.Batch050_099
import ForestUnimodality.BinomialMassData.Q405_808.Batch100_149
import ForestUnimodality.BinomialMassData.Q405_808.Batch150_199
import ForestUnimodality.BinomialMassData.Q203_404.Batch000_049
import ForestUnimodality.BinomialMassData.Q203_404.Batch050_099
import ForestUnimodality.BinomialMassData.Q203_404.Batch100_149
import ForestUnimodality.BinomialMassData.Q203_404.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel000
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
  base := (919390714842854574373376401/10000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (46)
      previous := (23)
      next := (23)
      square := (153611824969293320197749607500000000000)
      linear := (-1265535682907462545088855825000000000)
      constant := (229847678710713643593344100250000000000000) }

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
  base := (919390714842854574373376401/10000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (46)
      previous := (23)
      next := (23)
      square := (153611824969293320197749607500000000000)
      linear := (-1265535682907462545088855825000000000)
      constant := (229847678710713643593344100250000000000000) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel001
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
  base := (127794571236570122565329070791706427870123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-1583782654593574841094688341967700000000000)
      constant := (1304032582332493429271557644217296653515624723) }

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
  base := (255086258095992104931371801427608400294701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-3175322706348098994859363039114150000000000)
      constant := (2602939166188163739311208357715456716406244901) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel002
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
  base := (299000675648128358319316868102058833838287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-12618622318743242627067701062658300000000000)
      constant := (3056456703921313797182117200999170663984365687) }

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
  base := (11918333091440581989486237597036314547287/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-12649651907387039877747646483373300000000000)
      constant := (3045854980896007333709880720381613567421867175) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel003
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
  base := (37282757590845459056735077218451189587007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-18902114019112185889756648757445800000000000)
      constant := (1915857552046442573297440585144115831135292035) }

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
  base := (2319848496482227166694294557964039904491/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-4737164600519470441444141722129575000000000)
      constant := (476875682414411255070407791585258871314253820) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel004
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
  base := (4990174872143877164123321036946048402687/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-25185605719481129152445596452233300000000000)
      constant := (1297919059833299270136799546112396743895252175) }

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
  base := (62077709329734388315748583065020000724749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-12623832448384361826902743646831650000000000)
      constant := (645966986819153015482133336619163977393164549) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel005
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
  base := (22357635177206447013005833222673609443643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-7867274354962518103783636036755200000000000)
      constant := (237944848305949866157050182363173997747102243) }

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
  base := (44502949842852439763346473239579195211171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-15773335695729782770917203849404150000000000)
      constant := (473821302339578143637393089217733245349155371) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel006
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
  base := (13589571623466855803626108230652626316311/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-37752589120219015677823491841808300000000000)
      constant := (749982804945078727432400957829923955263442555) }

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
  base := (33821217315977776622822521752099732126927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-18922838943075203714931664051976650000000000)
      constant := (373573933302827492387229200915713042426782327) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel007
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
  base := (1685577476409953898408201594937423362279/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-11009020205146989735128109884148950000000000)
      constant := (156892727588878376674564363094034472311364632) }

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
  base := (26855250477049656915411691632573534682363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-22072342190420624658946124254549150000000000)
      constant := (312813637472609432806259529582050977294784963) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel008
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
  base := (22061881610949123912188536690314951659867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-25159786260478451101600693615691650000000000)
      constant := (275549146968687346229920740813321071882303267) }

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
  base := (43945342890132798251547845696320187755131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-50443690875532091205921168914243300000000000)
      constant := (549777056169651623513000245643482035290091331) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel009
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
  base := (18395077202622632433008649565200976503043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-28301532110662922732945167463085400000000000)
      constant := (251542487291126193038796238077325926932541643) }

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
  base := (3664390297842511194960598610543931224257/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-28371348685111466546975044659694150000000000)
      constant := (251112160556428251543788406481811537093228285) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel010
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
  base := (31021173028035682441676777985736759465201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-62886555921694788728579282620958300000000000)
      constant := (474181942185715750648553356533780683304515401) }

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
  base := (30896677469420984018927668875226549497947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-63041703864913774981979009724533300000000000)
      constant := (473691222025620185823427307692673281428557347) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel011
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
  base := (13154767897537866742115287082377216914159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-34585023811031865995634115157872900000000000)
      constant := (229607199926746584160491326426535942866335959) }

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
  base := (13100346598413225243690271847751809945953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-34670355179802308435003965064839150000000000)
      constant := (229523464819288972620414812158252013258666553) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel012
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
  base := (2795097008802029953058160921107133717943/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-18863384830608168813489294502633325000000000)
      constant := (113794623358066767637633617166632054613473086) }

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
  base := (695750574047578449567087142552143250961/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-18909929213573864689509212633705825000000000)
      constant := (113828361937631213114218290141542731424425288) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel013
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
  base := (18993398692141964272030764204873244348219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-81737031022801618516646125705320800000000000)
      constant := (460222790775340128879046889210407996846182019) }

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
  base := (9453296480879316474769807937163518852873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-40969361674493150323032885469984150000000000)
      constant := (230326992019389871565393498070125830818157473) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel014
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
  base := (804387984513431453818192693186416061513/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-22005130680792640444833768350027075000000000)
      constant := (118281700936225679963106303270335213717470565) }

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
  base := (16009559895644715474026924066576460584573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-88237729843677142534094691345113300000000000)
      constant := (473856077451785679583840162954773624423229173) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel015
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
  base := (13559593299210699314789290091322836702787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-94304014423539505042024021094895800000000000)
      constant := (493030937266216803764659049221258163455130187) }

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
  base := (6744536557372254314826863256152501628621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-47268368169183992211061805875129150000000000)
      constant := (247032207183918241200580921218384919113562821) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel016
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
  base := (11346052554676212526152446519248446308833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-100587506123908448304712968789683300000000000)
      constant := (519294089456540071549510054046026400796405433) }

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
  base := (1128250500454304920667162018641039626223/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-50417871416529413155076266077701650000000000)
      constant := (260320065245632505940054287663586026135504115) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel017
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
  base := (1879628378539959680314927979386510900989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-106870997824277391567401916484470800000000000)
      constant := (551416456567861780686106779716554519754943945) }

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
  base := (9340974379959244842970947095495493134799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-107134749327749668198181452560548300000000000)
      constant := (553084588853059044834799740435335975468084599) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel018
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
  base := (7676447464500093993791960610618596624401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-113154489524646334830090864179258300000000000)
      constant := (588995977928763247749410084262911804165514601) }

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
  base := (7625129520724682544190476611379361584523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-113433755822440510086210372965693300000000000)
      constant := (590996362554760500309756424123187917523719123) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel019
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
  base := (6148596103495704566583939414939103266537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-119437981225015278092779811874045800000000000)
      constant := (631702414866947665035234960913104698671943937) }

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
  base := (3051317619760562677673094978198105996043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-59866381158565675987119646685419150000000000)
      constant := (317022800175268021563593325419879579265634643) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel020
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
  base := (299227692399509726444556378055995312221/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-31430368231346055338867189892208325000000000)
      constant := (169815226044620024550335073632672770219865684) }

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
  base := (1186643736839959267193427187988376258491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-31507942202955548465567053443995825000000000)
      constant := (170489431529027893808176524186256801212866691) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel021
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
  base := (446372165887353811077961753274425804421/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-33001241156438291154539426815905200000000000)
      constant := (182860197604743541637137188550247343074297242) }

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
  base := (3534362702258450098733082684648796988689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-132330775306513035750297134181128300000000000)
      constant := (734502340657324964884181528691973728081616489) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel022
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
  base := (49590593811860643647758345132257100563/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-69144228163061053940423327479204150000000000)
      constant := (394023774548619669088224975502808742071079075) }

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
  base := (305869289878884226260713851064417341221/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-34657445450300969409581513646568325000000000)
      constant := (197871293560273735428141019607697980095590842) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel023
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
  base := (93573114087859099860537781178045686523/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-36142987006622762785883900663298950000000000)
      constant := (212229158644887047495560045529019702755384492) }

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
  base := (293649036610522691686574812540085859849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-144928788295894719526354974991418300000000000)
      constant := (852741943693630914230242412821723379281598245) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel024
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
  base := (305114414667191131704065310076916244479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-75427719863429997203112275173991650000000000)
      constant := (456954305197266058484800156776599372609930279) }

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
  base := (584592858846511579791877320330734815621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-151227794790585561414383895396563300000000000)
      constant := (918133482530636519747129058875533225854149821) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel025
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
  base := (-192888727764849499051390949356704099207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-157138931427228937668913498042770800000000000)
      constant := (982905191559294300227601544417581792733989393) }

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
  base := (-215571264551540367113726903656756498173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-157526801285276403302412815801708300000000000)
      constant := (987541779351664846833662975797093676962137227) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel026
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
  base := (-922025568458643825768889861552088834189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-163422423127597880931602445737558300000000000)
      constant := (1055805972460931892873286633330510141802438011) }

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
  base := (-942063218090504683174526250017504919563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-163825807779967245190441736206853300000000000)
      constant := (1060866700825005531058459279063058282315537837) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel027
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
  base := (-1585539778555440980923279802943267934103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-169705914827966824194291393432345800000000000)
      constant := (1132525692266112995771766481775885630054215297) }

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
  base := (-400803742974636061727127505107073689051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-42531203568664521769617664152999575000000000)
      constant := (284505813130845295724438989951755541297990749) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel028
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
  base := (-8556759079008335793517416487219715501/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-43997351632083941864245085281783325000000000)
      constant := (303247983605232082361014576453610350159155136) }

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
  base := (-441220063869268634194540357608303796563/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-176423820769348928966499577017143300000000000)
      constant := (1218939274680617453718338720559257764856304185) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel029
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
  base := (-2743027529294080454329360981871946453941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-182272898228704710719669288821920800000000000)
      constant := (1297143183592055822177009062908468305473347859) }

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
  base := (-1378362813998090111977841478989702608283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-91361413632019885427264248711144150000000000)
      constant := (651776748170605768900917721203056618692905117) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel030
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
  base := (-3248154342602413012085494856560545327667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-188556389929073653982358236516708300000000000)
      constant := (1384927180578346678750586976254097127112468933) }

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
  base := (-3260191293008586003581365463062998912671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-189021833758730612742557417827433300000000000)
      constant := (1391813888374130862520864499720881098091843129) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel031
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
  base := (-927565767488935736367789035326021112619/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-48709970407360649311261796052873950000000000)
      constant := (369074881877072014800261891352757235192673581) }

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
  base := (-3720828580123442166822206703970525166899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-195320840253421454630586338232578300000000000)
      constant := (1483676267537562895092649854559242772772463301) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel032
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
  base := (-4133051401984602427179261468273818238699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-201123373329811540507736131906283300000000000)
      constant := (1571222504239757904834750387814484780147031501) }

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
  base := (-517789462986762558608307669556941683/1250000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-50404961687028074129653814659430825000000000)
      constant := (394775778091212223565629030243459075783434000) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel033
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
  base := (-451966092260839419354762410491969845963/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-103703432515090241885212539800535400000000000)
      constant := (834832031737597194169156705161603843631657185) }

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
  base := (-226388816972720995334794557558561015937/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-51979713310700784601661044760717075000000000)
      constant := (419515639561487091100563086887567107882133315) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel034
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
  base := (-2436380384200978674637341849944531298131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-106845178365274713516557013647929150000000000)
      constant := (885798488676198788002353925040673086227765669) }

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
  base := (-4879863250015211982390128206177179366351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-214217859737493980294673099448013300000000000)
      constant := (1780527544343347817379144207052213243283853449) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel035
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
  base := (-519461868978500827230414852463401612191/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-109986924215459185147901487495322900000000000)
      constant := (938499056274667970531264969505908653895198045) }

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
  base := (-2600414645461724867770139409974631770009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-110258433116092411091351009926579150000000000)
      constant := (943237544639826390608161412064459281314138191) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel036
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
  base := (-2743580708752143828939366716169014292037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-113128670065643656779245961342716650000000000)
      constant := (992923907242830990839804371448648260206930563) }

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
  base := (-5492587701764780929587682214959164276289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-226815872726875664070730940258303300000000000)
      constant := (1995885676097850063078923097371950665217575911) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel037
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
  base := (-5752025947138295110003872194231025918241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-232540831831656256821180870380220800000000000)
      constant := (2098129384169479423395484831837467335858023559) }

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
  base := (-2878381652780454848419326742619207684411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-116557439610783252979379930331724150000000000)
      constant := (1054371364989147629556644153253546937411323389) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel038
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
  base := (-2396241243831254393000596856465581671/4000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-59706080883006300020967454518752075000000000)
      constant := (553457158433717025123955181282579813358830625) }

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
  base := (-299736799395196603789372055795052850167/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-59853471429064336961697195267148325000000000)
      constant := (556258043677015849407684655684424966877232165) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel039
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
  base := (-6204074588597702370869965685527278883401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-245107815232394143346558765769795800000000000)
      constant := (2332933508825650539714437525797057134360426399) }

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
  base := (-6207677620846911518605085377766987752153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-245712892210948189734817701473738300000000000)
      constant := (2344742056020341178355677264261134857940287247) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel040
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
  base := (-6393444371456369360996838946342635626291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-251391306932763086609247713464583300000000000)
      constant := (2455433767767793855800196375877541273976205509) }

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
  base := (-6396583420242852503713369902127982859833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-252011898705639031622846621878883300000000000)
      constant := (2467862221718212102603723616254591446846843567) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel041
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
  base := (-1639891367483256493628099479513146226093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-64418699658283007467984165289842700000000000)
      constant := (645330177247035400460861681985615778160125307) }

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
  base := (-6562298575916518829286976542501773762059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-258310905200329873510875542284028300000000000)
      constant := (2594384050020273754869697749130335255853236141) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel042
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
  base := (-670316262312590490005769708016529022413/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-131979145166750486567312804427079150000000000)
      constant := (1355293469711576353093680592623179937211824935) }

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
  base := (-6705540867387891697669729048669000437563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-264609911695020715398904462689173300000000000)
      constant := (2724300218857642806908490316816853976536419837) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel043
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
  base := (-6824851586316634399335904873778688507419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-270241782033869916397314556548945800000000000)
      constant := (2843226177753199278934305726521591504785818781) }

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
  base := (-1365383974072379377875736591925288765537/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-270908918189711557286933383094318300000000000)
      constant := (2857604509948553310833046835760841446513785315) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel044
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
  base := (-6925155519292052473194965298502330163041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-276525273734238859660003504243733300000000000)
      constant := (2979233087225295785637630475028140980006818759) }

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
  base := (-3463476633967047378267178076336670477877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-138603962342201199587481151749731650000000000)
      constant := (1497145821203873727745692951547984074455176723) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel045
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
  base := (-7004518910299937189128171481963543261787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-282808765434607802922692451938520800000000000)
      constant := (3118603133614826642230836347571081926436510813) }

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
  base := (-7006080702971449418605902896092800774501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-283506931179093241062991223904608300000000000)
      constant := (3134357131438339339900802676131478089299315299) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel046
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
  base := (-7063319406217684161889982927236715192561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-289092257134976746185381399633308300000000000)
      constant := (3261332464545995536047813102759552518320685239) }

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
  base := (-1412935108465244700030633503162523320003/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-289805937673784082951020144309753300000000000)
      constant := (3277797168325069033028162182898581848063246985) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel047
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
  base := (-284075114551369091452774307249288279977/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-295375748835345689448070347328095800000000000)
      constant := (3407417806959208602427308529557020162648865575) }

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
  base := (-7103054867663145766536220100768421399943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-296104944168474924839049064714898300000000000)
      constant := (3424608518517874636738026348420047033299181457) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel048
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
  base := (-1424093377879794042940810184863138875267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-301659240535714632710759295022883300000000000)
      constant := (3556856379996585524712335237368574601667006665) }

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
  base := (-7121487960227319094191070746534399346237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-302403950663165766727077985120043300000000000)
      constant := (3574788435078774856587871433710921392269036363) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel049
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
  base := (-3559659047382802558611858571781806471417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-153971366118041787986724121358835400000000000)
      constant := (1854822910493568469537445285385774557810075183) }

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
  base := (-3560101753290894838779331151784205303949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-154351478578928304307553452762594150000000000)
      constant := (1864167292588070029174102690376842146694416251) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel050
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
  base := (-7098628261482144674794953103164392394469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-314226223936452519236137190412458300000000000)
      constant := (3865784122561781518156944326174457533184021731) }

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
  base := (-7099395718120335947901159628703928585627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-315001963652547450503135825930333300000000000)
      constant := (3885244987659542308241722845843777474498018973) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel051
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
  base := (-3529282289320680758709208198576492268569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-160254857818410731249413069053622900000000000)
      constant := (2012634789612291944179929897730274655493327631) }

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
  base := (-3529614764048407669972841831383482313211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-160650485073619146195582373167739150000000000)
      constant := (2022758980022429503288386234131917396922934589) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel052
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
  base := (-1399853818567032394874666694387886843333/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-326793207337190405761515085802033300000000000)
      constant := (4188100741958260013218659589649995581555800335) }

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
  base := (-6999845005229504014245941275699660778913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-327599976641929134279193666740623300000000000)
      constant := (4209152073491095018239545884233576460394308487) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel053
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
  base := (-1730215622248890865343673722304134589651/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-83269174759389837256051008374205200000000000)
      constant := (1088569094913954595768908772505742030863470149) }

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
  base := (-6921361101976769853418478778095361535201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-333898983136619976167222587145768300000000000)
      constant := (4376146114564222532459471704838639766979414599) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel054
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
  base := (-3411723651348009340701577248271757016369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-169680095368964146143446490595804150000000000)
      constant := (2261897723175937103453840323340257681676019831) }

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
  base := (-136477576755564433602647477159187026593/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-170098994815655409027625753775456650000000000)
      constant := (2273249526382469049818251334291841403543120175) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel055
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
  base := (-1676777662351465515671835272901768055327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-86410920609574308887395482221598950000000000)
      constant := (1174164263345381201053109004314358790630109273) }

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
  base := (-1676871000609208777110062141023673542479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-86624249031500414985820106989014575000000000)
      constant := (1180052503237865391382921994487216381193171721) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel056
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
  base := (-6571926543334951238319510658343500120809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-351927174138666178812270876581183300000000000)
      constant := (4872860445725815417274727098461593455267627391) }

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
  base := (-821531181497242166271145333405098694247/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-88199000655173125457827337090300825000000000)
      constant := (1224319562979869641865299949053218826439972706) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel057
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
  base := (-802244733447875335112831043450680153791/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-89552666459758780518739956068992700000000000)
      constant := (1263101245478561459589382709692285606314856018) }

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
  base := (-25672948233667168694509675361086103443/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-179547504557691671859669134383174150000000000)
      constant := (2538851569256280699556232563904862807347244625) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel058
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
  base := (-6245258048027988602688755138431576401819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-364494157539404065337648771970758300000000000)
      constant := (5235290116949434872923664576192908489125044381) }

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
  base := (-3122749682803052091886945895557254640887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-182697007805037092803683594585746650000000000)
      constant := (2630742068365434310711179245921923470408311713) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel059
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
  base := (-6053872475503296238897076818859826629029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-370777649239773008600337719665545800000000000)
      constant := (5421515387799491137786656784449116814807275171) }

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
  base := (-1210816199094055681671199416819787249319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-371693022104765027495396109576638300000000000)
      constant := (5448620791386149378498808502143517151348484405) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel060
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
  base := (-1460959928528578285424485132537972458939/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-94265285235035487965756666840083325000000000)
      constant := (1402770100267993893631704489092439205446363261) }

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
  base := (-584401984225430392148727931587539202541/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-188996014299727934691712514990891650000000000)
      constant := (2819556357959605268398391445139151812974396295) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel061
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
  base := (-1403798131963352274654663294745877363197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-95836158160127723781428903763780200000000000)
      constant := (1450996205635350504735395508549957312830527403) }

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
  base := (-561534808674296700771755209146482628321/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-192145517547073355635726975193464150000000000)
      constant := (2916479791026933245713794503831693828542487395) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel062
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
  base := (-5367958752836461412617433616939731614591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-389628124340879838388404562749908300000000000)
      constant := (6000228368251552406663472227434315047799557209) }

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
  base := (-5368093057588976108120873492738311025447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-390590041588837553159482870792073300000000000)
      constant := (6030161111010530963583830387805602439229415153) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel063
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
  base := (-5102162038375417627034004512126580321797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-395911616041248781651093510444695800000000000)
      constant := (6199810796955795560802880025135864660387348803) }

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
  base := (-5102277962797604652407098769427625583917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-396889048083528395047511791197218300000000000)
      constant := (6230717066044342159009036797302434091418462683) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel064
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
  base := (-4817822476610562800760753663213467656937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-402195107741617724913782458139483300000000000)
      constant := (6402731903694208433474044179370251416431585663) }

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
  base := (-240896125547058424831181612813270334743/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-100797013644554809233885177900590825000000000)
      constant := (1608656811527038470913917166133818746576433285) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel065
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
  base := (-1128739284365063484812978562270553444439/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-102119649860496667044117851458567700000000000)
      constant := (1652247878584138466216081514369925467125777761) }

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
  base := (-4515043438726090974247558867963905669001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-409487061072910078823569632007508300000000000)
      constant := (6641891480470823913098926246289145448270520799) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel066
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
  base := (-4193580523125968878561479387902076286749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-414762091142355611439160353529058300000000000)
      constant := (6818589480945874579568138875665771419798873451) }

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
  base := (-4193654959029522768900422330263459275929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-415786067567600920711598552412653300000000000)
      constant := (6852509624146792433215186175017768301926248271) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel067
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
  base := (-1926852477124763385308410052179145584723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-210522791421362277350924650611922900000000000)
      constant := (3515762838919651690208335761052822989015240677) }

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
  base := (-963442285348607223975667585915253720393/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-105521268515572940649906868204449575000000000)
      constant := (1766620388503662914470791140932093546798271007) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel068
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
  base := (-1747670449000146385220403908592991009809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-213664537271546748982269124459316650000000000)
      constant := (3623899999120622786731767842728404273708938391) }

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
  base := (-139815849406591632623865134744371752229/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-428384080556982604487656393222943300000000000)
      constant := (7283807165520843632225909350398884893887799275) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel069
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
  base := (-62369944936493381833184564221651246861/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-216806283121731220613613598306710400000000000)
      constant := (3733706175719927704863767362974830406394273475) }

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
  base := (-3118544943907741168005472712742498645921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-434683087051673446375685313628088300000000000)
      constant := (7504486369880280036182544113515123921312959879) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel070
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
  base := (-2723181555277066473299584703031704644729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-439896057943831384489916144308208300000000000)
      constant := (7690362660371123345259849081227552330919119471) }

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
  base := (-272322265846598432640834061058344273109/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-220491046773182144131857117016616650000000000)
      constant := (3864259545849487221220624187073862025350075455) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel071
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
  base := (-2309400241235897523253053166424003792887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-446179549644200327752605092002995800000000000)
      constant := (7916650859566271693047380866206025643558759713) }

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
  base := (-2309435654876881041307682214386768186989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-447281100041055130151743154438378300000000000)
      constant := (7955905266955069733986146638293535677724525211) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel072
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
  base := (-5866121115188264361872882192274121113/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-113115760336142317753823509924445825000000000)
      constant := (2036569223351956413498530744113411060242102960) }

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
  base := (-234648657806808805001225251160830988417/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-113395026633936493009943018710880825000000000)
      constant := (2046661210321058349419896823474926276174316366) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel073
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
  base := (-178307716729687854908459879134947008731/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-114686633261234553569495746848142700000000000)
      constant := (2094810178661985527547992089012792193940370138) }

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
  base := (-1426488006532313028785073153453748859449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-459879113030436813927800995248668300000000000)
      constant := (8420737768523537782797106264379733357884760751) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel074
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
  base := (-957313106788050250754204410160479120929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-465030024745307157540671935087358300000000000)
      constant := (8615542283149558585692539882216924952487403271) }

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
  base := (-957335729687001446172821667890044136841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-466178119525127655815829915653813300000000000)
      constant := (8658184009474859067832963884993379309760084959) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel075
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
  base := (-4697162181116404321177044507982261789/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-117828379111419025200840220695536450000000000)
      constant := (2213795391204213798500818968690252800249760275) }

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
  base := (-469735694686359139122530892043075065479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-472477126019818497703858836058958300000000000)
      constant := (8898983530854702685804828476194938591257048721) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel076
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
  base := (7265218586744391465213010503341104807/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-477597008146045044066049830476933300000000000)
      constant := (9098158530686561029594496308844232163050681035) }

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
  base := (7261865616535336219490011143327781043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-478776132514509339591887756464103300000000000)
      constant := (9143136304402351490220551608627913533472098215) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel077
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
  base := (1402028536373309848861333970584309281/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-120970124961603496832184694542930200000000000)
      constant := (2336118289038979355344322733169565061710048100) }

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
  base := (22431879454671899026709835541862769859/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-485075139009200181479916676869248300000000000)
      constant := (9390642306122469480675636834991223502883291475) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel078
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
  base := (1103737698095161000393106270816057893691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-490163991546782930591427725866508300000000000)
      constant := (9594125420326747683302870733835734856573541891) }

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
  base := (551862641496350815048800177892339540469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-245687072751945511683972798637196650000000000)
      constant := (4820750757820945903700331975385932530652324269) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel079
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
  base := (1665103203459622220809318374752472238923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-496447483247151873854116673561295800000000000)
      constant := (9847115305448173272385879509651715875559253523) }

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
  base := (832546261159825892465318470099908081999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-248836575999290932627987258839769150000000000)
      constant := (4947856957831693654295909229558781612344471799) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel080
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
  base := (448981290529044493444811288502603889319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-502730974947520817116805621256083300000000000)
      constant := (10103442796443141842778778733745940311374715595) }

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
  base := (2244897264765134191344091326439398366663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-503972158493272707144003438084683300000000000)
      constant := (10153279491501774761497359341247406302738329263) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel081
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
  base := (88848318447963775208538833286108827947/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-127253616661972440094873642237717700000000000)
      constant := (2590776970126540860961100462097347152043598776) }

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
  base := (2843138288186576139900900990873909929331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-510271164987963549032032358489828300000000000)
      constant := (10414198230689977781908319122357849605189105531) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel082
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
  base := (345982135038872084704065060141626843293/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-257648979174129351821091758322829150000000000)
      constant := (5313055273380773210313385613827365427142159465) }

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
  base := (1729907277542772281845762706114823523469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-258285085741327195460030639447486650000000000)
      constant := (5339235061322237427054576789795690039762907269) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel083
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
  base := (409493102738034617733578459471732532721/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-260790725024313823452436232170222900000000000)
      constant := (5446225392986517439608686412674607170956434605) }

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
  base := (1023731296189164768377521132176414152729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-130717294494336308202022549825029575000000000)
      constant := (2736523789595297598187393382609391550771988529) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel084
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
  base := (2374237226206711892885146536889675393613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-263932470874498295083780706017616650000000000)
      constant := (5581064295148558867301476833547109453690246213) }

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
  base := (4748469429635775071139452077294636094463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-529168184472036074696119119705263300000000000)
      constant := (11217073330274222558783166069887470482799617063) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel085
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
  base := (5420450972576159795029641030837725980441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-534148433449365533430250359730020800000000000)
      constant := (11435143953073441777441028181275537673976478641) }

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
  base := (1355111663803591966346192267413112741229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-133866797741681729146037010027602075000000000)
      constant := (2872851157962737472958763110350248600573277029) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel086
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
  base := (1527715008371456961304716870395161080703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-135107981287433619173234826856202075000000000)
      constant := (2927874217161687204033576967723051475684251303) }

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
  base := (48886850583859870476125152457012571319/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-541766197461417758472176960515553300000000000)
      constant := (11769089057618032354754935921810433505003139875) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel087
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
  base := (6819701164458887700114340146076972970051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-546715416850103419955628255119595800000000000)
      constant := (11991187332215596056733075463056646107517490251) }

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
  base := (1363939595188734607490713014911230078931/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-548065203956108600360205880920698300000000000)
      constant := (12050126602913649162458949610559181990175875655) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel088
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
  base := (3773486982955899703383549390966500462041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-276499454275236181609158601407191650000000000)
      constant := (6137107669851915904088649307168100021213280241) }

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
  base := (235842850822317159401628104862983666759/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-138591052612699860562058700331460825000000000)
      constant := (3083629315945504477346877886749487821076868472) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel089
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
  base := (4146339049328528326288804699861230904847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-279641200125420653240503075254585400000000000)
      constant := (6280290443825702159286074739252365182085344247) }

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
  base := (1036584468134609435287702033247420633741/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-140165804236372571034065930432747075000000000)
      constant := (3155565259216708951506631522256497538269583882) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel090
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
  base := (4528406637404706093297109564488277075077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-282782945975605124871847549101979150000000000)
      constant := (6425141986560798090355335122315292414442860477) }

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
  base := (70756337914929075976954603938975904779/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-141740555860045281506073160534033325000000000)
      constant := (3228339479830197560196666708600479095048818528) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel091
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
  base := (1967875850012026201952756148108495767957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-571849383651579193006384045898745800000000000)
      constant := (13143324593622213988867519757829175732894646785) }

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
  base := (9839377513658591134570173925745751517951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-573261229934871967912321562541278300000000000)
      constant := (13207807908728715949687057281127302011234618151) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel092
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
  base := (5320187908556762145847367251111974304969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-289066437675974068134536496796766650000000000)
      constant := (6719851373519317210641936858636184374884988769) }

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
  base := (5320187162964312893455917016131664396009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-289780118214781404900175241473211650000000000)
      constant := (6752805501521170655322743085631252958503687809) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel093
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
  base := (11459802800110957892741519567652695266619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-584416367052317079531761941288320800000000000)
      constant := (13739418431576923551101207756766361175664780419) }

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
  base := (11459801519664200980545644459531336293193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-585859242924253651688379403351568300000000000)
      constant := (13806767200524876454881650818607418711526861793) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel094
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
  base := (12297660049893817463320574239149893598131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-590699858752686022794450888983108300000000000)
      constant := (14042471645715514353339419963433131314594534331) }

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
  base := (12297658950530243927491777769178968557241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-592158249418944493576408323756713300000000000)
      constant := (14111276499703959304885369003463219808252415441) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel095
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
  base := (13153947439979247027488292102835429059629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-596983350453054966057139836677895800000000000)
      constant := (14348862388164155214187909608244688118087275429) }

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
  base := (13153946496196541379680860656435190554231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-598457255913635335464437244161858300000000000)
      constant := (14419138899331699355313085048747939878843710431) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel096
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
  base := (14028664863141454193012675384306348346803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-603266842153423909319828784372683300000000000)
      constant := (14658590657829035825453518081904347059485737403) }

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
  base := (3507166013252931212229883700562774913467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-151189065602081544338116541141750825000000000)
      constant := (3682588599587687249054184626562240266892276867) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel097
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
  base := (14921812228507497732472247638357968235927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-609550333853792852582517732067470800000000000)
      constant := (14971656453783161313675318903194575165224691327) }

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
  base := (14921811533179038464207818022831679816563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-611055268903017019240495084972148300000000000)
      constant := (15044922995865493520956258557709390415808759163) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel098
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
  base := (247396710298283927614113100516223371483/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-153958456388540448961301669940564575000000000)
      constant := (3822014943810296296901420762484757538799969328) }

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
  base := (15833388862358226553496970716680582674951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-617354275397707861128524005377293300000000000)
      constant := (15362844691117587981421076010454363673867175151) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel099
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
  base := (2095424561211529468605117892169377445237/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-155529329313632684776973906864261450000000000)
      constant := (3901950155384507602162220467549239865200225274) }

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
  base := (8381697988814642586227164126234355159789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-311826640946199351508276462891219150000000000)
      constant := (7842059741732592708687526676289846356985007589) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel100
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
  base := (17711833265126138631922858783974480289321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-628400808954899682370584575151833300000000000)
      constant := (15930878992110728756352012671198592423431363521) }

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
  base := (8855916412881754640682713809988987832829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-314976144193544772452290923093791650000000000)
      constant := (8004373686182649904354031673459071414882688629) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel101
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
  base := (18678699738701764261430332847086941191689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (184)
      previous := (92)
      next := (92)
      square := (614447299877173280790998430000000000000)
      linear := (-62217851255295424530268946460800000000000)
      constant := (1593696195126261578266553286788368191191689) }

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
  base := (18678699361755494328523699637618482633563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (184)
      previous := (92)
      next := (92)
      square := (614447299877173280790998430000000000000)
      linear := (-62371463080264717850466696068300000000000)
      constant := (1601483026895287817232442631236968482633563) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel102
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
  base := (19663995870941890647880953983318812940983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-640967792355637568895962470541408300000000000)
      constant := (16587048304252120077769464014071859960810967583) }

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
  base := (9831997773788368895554198840051685069607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-321275150688235614340319843498936650000000000)
      constant := (8334031219028925153890005359622829714395061007) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel103
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
  base := (20667721628491097677460803301144284597309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-647251284056006512158651418236195800000000000)
      constant := (16920139245077847269388058691217285753427149109) }

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
  base := (20667721351117419721545974306935829237393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-648849307871162070568668607403018300000000000)
      constant := (17002749614134805387998455903469666694050645993) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel104
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
  base := (21689876983189021298619616385751701805419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-653534775756375455421340365930983300000000000)
      constant := (17256567708672912061063029862668927610117079219) }

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
  base := (21689876745287980332652344290020562102053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-655148314365852912456697527808163300000000000)
      constant := (17340789885313355664854417980508537154003042653) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel105
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
  base := (710326934727600827898380226448397283117/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-164954566864186099671007328406442700000000000)
      constant := (4399083423698753965792386203523678188293112136) }

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
  base := (1136523085362819598811312501451104951927/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-165361830215135938586181612053327075000000000)
      constant := (4420545812840147906077148980395312170573036635) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel106
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
  base := (371710568636885795140610430100127055191/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-166525439789278335486679565330139575000000000)
      constant := (4484859300810001458625647334217426837440054256) }

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
  base := (23789476217800657047044146995418178846883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-667746327355234596232755368618453300000000000)
      constant := (18026929712080429668790104348952345692417053483) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel107
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
  base := (24866920410780050719888026785102049818613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-672385250857482285209407209015345800000000000)
      constant := (18285878233836083223270056184207025916449671213) }

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
  base := (194272814537180856512903896632013811553/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-168511333462481359530196072255899575000000000)
      constant := (4593757316827001263094049394199558832532868896) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel108
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
  base := (25962793951189445445016446132398051417857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-678668742557851228472096156710133300000000000)
      constant := (18635656786438884900099339248829447772513559257) }

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
  base := (12981396911282019867023014735302240119823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-340172170172308140004406604714371650000000000)
      constant := (9363240958452456170608222134139351801462314423) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel109
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
  base := (6769274250529269564245984032987330801931/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-171238058564555042933696276101230200000000000)
      constant := (4747193215231826666439536789524199769322998131) }

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
  base := (27077096891845264702331397224200238567399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-686643346839307121896842129833888300000000000)
      constant := (19081287660755165526260061960513225783626037199) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel110
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
  base := (14104914776811773770989769653453584965441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-345617862979294557498737026049854150000000000)
      constant := (9672613228599978342191997167393873145232463641) }

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
  base := (28209829459094402861638471094067907592221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-692942353333997963784871050239033300000000000)
      constant := (19439446498761769197981306608627571475348246421) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel111
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
  base := (29360991597406650783058031747918211660223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-697519217658958058260162999794495800000000000)
      constant := (19705017575172144188101522549802975583395934823) }

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
  base := (29360991516379409498855785753301807674057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-699241359828688805672899970644178300000000000)
      constant := (19800958430843808568261728154821975840083055457) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel112
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
  base := (7632645781637690298707479099204867308653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-175950677339831750380712986872320825000000000)
      constant := (5017036553693330717018243385913041601415569253) }

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
  base := (3816322882137817338935646980876305413453/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-176385091580844911890232222762330825000000000)
      constant := (5041455864233495007787485703577797683045268106) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel113
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
  base := (31718604135314065801536999148001657959721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-710086201059695944785540895184070800000000000)
      constant := (20434612375944920490132637978263998444097113921) }

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
  base := (31718604075794932292929208872896339592831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-711839372818070489448957811454468300000000000)
      constant := (20534041576976495764080450178139279610186469031) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel114
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
  base := (8231263654736990838467432652805764498721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-179092423190016222012057460719714575000000000)
      constant := (5201104014659624143234077285077153978651452921) }

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
  base := (3292505456794234000609744377119089645489/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-359069189656380665668493365929806650000000000)
      constant := (10452806395462652950192345328527771492368166445) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel115
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
  base := (17074967286771889151695708628049823608017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-361326592230216915655459395286822900000000000)
      constant := (10588778631407089358607192159541285703750381417) }

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
  base := (34149934529837270521518722992915242587119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-724437385807452173225015652264758300000000000)
      constant := (21280537098742590321010728972902847389631200919) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel116
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
  base := (69127429679497413779003639250709012471/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-182234169040200693643401934567108325000000000)
      constant := (5388508997109833902305123966342535214935733888) }

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
  base := (35393243958453581333270255622730940029791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-730736392302143015113044572669903300000000000)
      constant := (21658814500397479346255646735553825419243897991) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel117
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
  base := (18327491441712641149705832010820979200819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-367610083930585858918148342981610400000000000)
      constant := (10966926117743725518875417108860413824452554619) }

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
  base := (18327491425670059046534080544993163633109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-368517699398416928500536746537524150000000000)
      constant := (11020222497932484375306300039653629737221344909) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel118
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
  base := (1896757561700902044073884836667991942793/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-185375914890385165274746408414502075000000000)
      constant := (5579251500984292157585383181371612866542156965) }

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
  base := (18967575603265262568876889939752555841861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-371667202645762349444551206740096650000000000)
      constant := (11212714292562499869980853759224418097142824061) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel119
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
  base := (4904218630751722546830334298880562601159/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-186946787815477401090418645338198950000000000)
      constant := (5675874323442870393328007763891788964751345918) }

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
  base := (19616874511233391608136084824838684709523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-374816705893107770388565666942669150000000000)
      constant := (11406882634080839479961478793075896372721844123) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel120
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
  base := (20275388159052176619322599194115754180181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-377035321481139273812181764523791650000000000)
      constant := (11546663052488522726802061340389198558392026381) }

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
  base := (20275388148967199586827849867589861511657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-377966209140453191332580127145241650000000000)
      constant := (11602727522481308682911262740999582677280413057) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel121
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
  base := (8377246609856704561868964156792386329047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-760354134662647490887052476742370800000000000)
      constant := (23486492437543595651006910891674453195963042235) }

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
  base := (41886233032007485493620159726608459980959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-762231424775597224553189174695628300000000000)
      constant := (23600497915518369979106795975604626750265762759) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel122
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
  base := (21620059619399276513963908690526636257597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-383318813181508217074870712218579150000000000)
      constant := (11941498145731726752492218443859932716463746997) }

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
  base := (43240119224002233522001095796962094861593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-768530431270288066441218095100773300000000000)
      constant := (23998893879821961267694637473478934779683110193) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel123
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
  base := (22306217443054593520969091833514104214231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-386460559031692688706215186065972900000000000)
      constant := (12141418833365553927692398483441426330214370431) }

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
  base := (44612434873437510010333947086543969570613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-774829437764978908329247015505918300000000000)
      constant := (24400642937868483191318462990292323833589823213) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel124
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
  base := (46003179990852898810057081538597913502997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-779204609763754320675119319826733300000000000)
      constant := (24686016563342860574060497661671765565644072397) }

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
  base := (23001589990000749189480597053078574990217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-390564222129834875108637967955531650000000000)
      constant := (12402872544827377454524593084867747993475203617) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel125
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
  base := (23706177276407734941506004708022769971957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-392744050732061631968904133760760400000000000)
      constant := (12546266490648263209305255091735956292108933357) }

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
  base := (47412354543523468937113207356844737154249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-787427450754360592105304856316208300000000000)
      constant := (25214200335179034807311266021289591913710494049) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel126
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
  base := (48839958571906086290512817070916575074537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-791771593164492207200497215216308300000000000)
      constant := (25502386920591178995723904709802829232335351937) }

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
  base := (12209989640987475143572284827717679558743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-198431614312262858498333444180338325000000000)
      constant := (6406502168610194229314120849831044136678737343) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel127
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
  base := (50285992048136271741481464175473440918821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-798055084864861150463186162911095800000000000)
      constant := (25915578381226935858755394151281264477062893021) }

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
  base := (12571498010331073464087308599982274232441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-200006365935935568970340674281624575000000000)
      constant := (6510292526860106247039294664321740104445130641) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel128
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
  base := (51750454981602076372958215775548232309001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-804338576565230093725875110605883300000000000)
      constant := (26332107363204776815152926251639751517784119201) }

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
  base := (51750454975770115166077950585217314241697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-806324470238433117769391617531643300000000000)
      constant := (26459684634179238500584136050840118622579551097) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel129
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
  base := (53233347372469027806920487929592001717047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-810622068265599036988564058300670800000000000)
      constant := (26751973866526390412188292632090549540765596447) }

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
  base := (53233347367476396192484414676640883348499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-812623476733123959657420537936788300000000000)
      constant := (26881552254659145766796937682571497301038038299) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel130
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
  base := (1710458413154982050812652067771250569229/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-204226389991491995062813251498864575000000000)
      constant := (6793794472798511081975992275409039341453640232) }

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
  base := (54734669216685584963990235990548702213153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-818922483227814801545449458341933300000000000)
      constant := (27306772968882619999133512389117171561276373753) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel131
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
  base := (28127210263670811770097073363418855589621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-411594525833168461756970976845122900000000000)
      constant := (13800859718605238019247745082329934198994723821) }

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
  base := (28127210261841652832079052638848595995819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-412610744861252821716739189373539150000000000)
      constant := (13867673388426287424945191589412803827753349619) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel132
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
  base := (1155852025838419943406729223166193348317/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-414736271683352933388315450692516650000000000)
      constant := (14015799252289400340335563805573265833654542925) }

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
  base := (7224075161098717037570368644402794817837/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-207880124054299121330376824788055825000000000)
      constant := (7041818419643069113730705469529552494873510474) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel133
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
  base := (11869842303006468190226904842004976340067/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-835756035067074810039319849079820800000000000)
      constant := (28464815093302433492459283834229569849475117335) }

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
  base := (59349211512352357306989545059366078727123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-837819502711887327209536219557368300000000000)
      constant := (28602553674045269462135867001622081919095381723) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel134
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
  base := (15231062799258369092775572259468797028649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-210509881691860938325502199193652075000000000)
      constant := (7225342300846256152716072417513058885989248449) }

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
  base := (30462125597369930763045764428514176819651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-422059254603289084548782569981256650000000000)
      constant := (14520593381637657453608714144407735192737259851) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel135
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
  base := (31258860169149943326148377904536809397517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-424161509233906348282348872234697900000000000)
      constant := (14670630417415202170117174288660134445789070917) }

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
  base := (7814715042042130968228148600283478485409/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-212604378925317252746398515091914575000000000)
      constant := (7370793236566584530650861959044506903059314418) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel136
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
  base := (32064809469610110452741301741261705539241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-427303255084090819913693346082091650000000000)
      constant := (14892244993821268645074185523046720908205797441) }

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
  base := (32064809468770273449587978983187184528889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-428358261097979926436811490386401650000000000)
      constant := (14964256111511192570220655023234990769379196689) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel137
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
  base := (65759947000192534521941946014818610369453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-860890001868550583090075639858970800000000000)
      constant := (30231056661825484023652825920842970175628790053) }

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
  base := (32879973499377626452719414445713280052367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-431507764345325347380825950588974150000000000)
      constant := (15188602296773793141800871569306537894814195767) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel138
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
  base := (16852176130405288178620834490941388605217/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-216793373392229881588191146888439575000000000)
      constant := (7670240214345842265560893316653259105161818617) }

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
  base := (16852176130097837386540959319363780139199/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-217328633796335384162420205395773325000000000)
      constant := (7707312514461531459210084756695830933699968999) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel139
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
  base := (8634486437989257654398637320407438308889/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-218364246317322117403863383812136450000000000)
      constant := (7783550643580088567144401205477151532940453378) }

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
  base := (17268972875715460312720506374582827437331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-218903385420008094634427435497059575000000000)
      constant := (7821162153980554214585685968559146522688213531) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel140
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
  base := (17690376986870185708254789042488549660543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-219935119242414353219535620735833325000000000)
      constant := (7897695453160154194044265203973976007587199143) }

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
  base := (70761507946580509659362629987783357301499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-881912548174723220425738662393383300000000000)
      constant := (31743400267780080334616243661833324527832591299) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel141
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
  base := (36232776926365195179388449403510300138269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-443011984335013178070415715319060400000000000)
      constant := (16025349286174165380656493304899648587335482069) }

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
  base := (18116388462990057426042590036312261595973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-222052888667353515578441895699632075000000000)
      constant := (8051376253355982000711982747539300968040520573) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel142
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
  base := (74188029220070437907952656942655324219387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-892307460370395299403520378332908300000000000)
      constant := (32513952853447652459193479064724859212361966787) }

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
  base := (74188029219411589038779337787319765493031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-894510561164104904201796503203673300000000000)
      constant := (32670962852857948267690895375859272877794409231) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel143
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
  base := (37964467024952680146896179033560278970671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-449295476035382121333104663013847900000000000)
      constant := (16490272327971353958694229943500377358904814871) }

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
  base := (75928934049341763193423123897882806909509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-900809567658795746089825423608818300000000000)
      constant := (33139773786086294726729049374536165813283901309) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel144
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
  base := (77688268342635698701637739212157204778749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-904874443771133185928898273722483300000000000)
      constant := (33450473979837583056529600136087772645948018549) }

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
  base := (7768826834215360610331781081845127261431/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-453554287076743293988927172006981650000000000)
      constant := (16805968906556538446477766172081828915969288155) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel145
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
  base := (15893206419731455358676435838471701080853/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-911157935471502129191587221417270800000000000)
      constant := (33923740825136315673791874169273578644878907265) }

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
  base := (19866508024561230454320734414838928673617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-228351895162044357466470816104777075000000000)
      constant := (8521863733485588191368088100801557723899567017) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel146
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
  base := (81262225318360576979587709156743776902451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-917441427171871072454276169112058300000000000)
      constant := (34400345191842889080245425266309318768181902651) }

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
  base := (81262225318007888425026979159793057793641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-919706587142868271753912184824253300000000000)
      constant := (34566325148578122952972625702478432832552931841) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel147
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
  base := (83076848002130251202368792929867719230437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-923724918872240015716965116806845800000000000)
      constant := (34880287079961227110351763072669275510119687837) }

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
  base := (415384240009143048396783582764193809671/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-231501398409389778410485276307349575000000000)
      constant := (8762137114256081524959683554334716602622693550) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel148
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
  base := (84909900150344744498559718522416494278239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-930008410572608958979654064501633300000000000)
      constant := (35363566489495190281931634160350458408132316039) }

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
  base := (84909900150086773554955484869040684152757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-932304600132249955529970025634543300000000000)
      constant := (35534124859284835403100422648434150319042274157) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel149
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
  base := (86761381763376012945279088602943860428289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-936291902272977902242343012196420800000000000)
      constant := (35850183420448572918927725395174784351478976089) }

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
  base := (86761381763155400179747805386116335479903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-938603606626940797417998946039688300000000000)
      constant := (36023054355363456041082649037318280888230490503) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel150
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
  base := (44315646420794660209134602720967826682237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-471287696986673422752515979945604150000000000)
      constant := (18170068936412550539068242001301739674985499637) }

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
  base := (44315646420700332142246857904744640228489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-472451306560815819653013933222416650000000000)
      constant := (18257668472631961681106948264312141949970816289) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel151
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
  base := (90519633385343100993335003327062403376313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-948858885673715788767720907585995800000000000)
      constant := (36833429846628431145565196117305070483091768913) }

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
  base := (90519633385181779614385764006652986147039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-951201619616322481194056786849978300000000000)
      constant := (37010972628989901705908874303148460211685944839) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel152
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
  base := (9242640339498887585741013191663222650749/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-477571188687042366015204927640391650000000000)
      constant := (18665029670931074494420885949721979421301452745) }

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
  base := (92426403394850934695252771529353074366981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-957500626111013323082085707255123300000000000)
      constant := (37509961406544983747319562169540166911617573181) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel153
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
  base := (94351602870871215323090082805430815522981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-961425869074453675293098802975570800000000000)
      constant := (37830026358529769569724997958778553280399929181) }

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
  base := (47175801435376635499659282190344656963281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-481899816302852082485057313830134150000000000)
      constant := (19006151638966345137302057688428512370682429481) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel154
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
  base := (96295231813327738005489288185175152515389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-967709360774822618555787750670358300000000000)
      constant := (38333330896634736935707656618096558730809483189) }

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
  base := (48147615906613447978080954081313223092589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-485049319550197503429071774032706650000000000)
      constant := (19258999121578235160825833456502338013767500389) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel155
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
  base := (98257290222689140462580745333745003379833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-973992852475191561818476698365145800000000000)
      constant := (38839972956180424522377630422629626685727676433) }

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
  base := (19651458044520584888329684425687875177077/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-976397645595085848746172468470558300000000000)
      constant := (39027046302219701591310921959985778073406812385) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel156
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
  base := (1566215282801238307084108065326599853619/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-245069086043890126270291411514983325000000000)
      constant := (9837488134292533927236466675630814884208278704) }

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
  base := (100237778099205543383481450053295950361707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-982696652089776690634201388875703300000000000)
      constant := (39539447455125691114431382327650818089639773107) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel157
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
  base := (51118347721707553730513037439831935397567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-493279917937964724171927296877360400000000000)
      constant := (19931634819803552289228088692206189588615580967) }

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
  base := (25559173860838023743522810544415520453259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-247248914646116883130557577320212075000000000)
      constant := (10013800425469419024679507249675697211643695059) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel158
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
  base := (5212702112770352064205711951934136501111/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-248210831894074597901635885362377075000000000)
      constant := (10094981065873624210476930512980714444739166555) }

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
  base := (104254042255353174703150523148600848196991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-995294665079158374410259229685993300000000000)
      constant := (40574309042478824928761013437266380802457505191) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel159
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
  base := (4251592741422351493620028028407747113699/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-999126819276667334869232489144295800000000000)
      constant := (40899916408835410892056822137279541613921087475) }

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
  base := (106289818535512741032850767410313707141719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-1001593671573849216298288150091138300000000000)
      constant := (41096769476932238284833150874146893026552675519) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel160
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
  base := (13543003035520949233763994306510893093653/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-251352577744259069532980359209770825000000000)
      constant := (10355811518908219739549741952866867740896708506) }

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
  base := (108344024284128234055990021638559103803907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-1007892678068540058186317070496283300000000000)
      constant := (41622583005240950353321074183483737417903655307) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel161
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
  base := (862630152355658936583177737008411504567/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-252923450669351305348652596133467700000000000)
      constant := (10487478315972467084479024005994599167071314944) }

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
  base := (27604164875372675228541387306671251146151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-253547921140807725018586497725357075000000000)
      constant := (10537937406851982526529054262288114145441886351) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel162
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
  base := (112507724187913681484463992977096572339731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-1017977294377774164657299332228658300000000000)
      constant := (42479917973609282685737173960758660634437595931) }

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
  base := (1406346552348561576537922890528175944887/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-255122672764480435490593727826643325000000000)
      constant := (10671067335859020657515697808630814318775845740) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel163
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
  base := (114617218343614142147472588143546712996737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-1024260786078143107919988279923445800000000000)
      constant := (43013260204793963342011144369582312925529714137) }

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
  base := (114617218343589565263968386600495198317307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-1026789697552612583850403831711718300000000000)
      constant := (43220142153328250490746388006050389318034848707) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel164
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
  base := (58372570984449142780224341893485860979977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-515272138889256025591338613809116650000000000)
      constant := (21774969978723345344061606367846429642856745377) }

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
  base := (23349028393775456153046144092541804989361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-1033088704047303425738432752116863300000000000)
      constant := (43759368057087215117597702977884280663482357805) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel165
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
  base := (5944574753201641496882945782640725803003/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-259206942369720248611341543828255200000000000)
      constant := (11022489307892546379144278252582390727394668015) }

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
  base := (118891495064014878718371232624099426330961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-1039387710541994267626461672522008300000000000)
      constant := (44301947054715698199556641778335805998002133161) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel166
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
  base := (121056277629278786857523571209601476462177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-1043111261179249937708055123007808300000000000)
      constant := (44633312027167110406484310545958861411390667577) }

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
  base := (121056277629263445863274913359831035712953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-1045686717036685109514490592927153300000000000)
      constant := (44847879146216363082456771193201919745307833553) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel167
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
  base := (385123405202786237096505536548948170847/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-262348688219904720242686017675648950000000000)
      constant := (11295001086060017774175728804583241849827319760) }

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
  base := (30809872416219621508347580885035226132183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-262996430882843987850629878333074575000000000)
      constant := (11349291082897954040225774997979977516774398783) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel168
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
  base := (125441131171121258258951245451579435534747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-1055678244579987824233433018397383300000000000)
      constant := (45730034182791617850302629074254128321889954147) }

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
  base := (125441131171110055485751887279437196633933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1876984)
      previous := (938492)
      next := (938492)
      square := (6267976906047044637348974984430000000000000)
      linear := (-1058284730026066793290548433737443300000000000)
      constant := (45949802610844608258773636334880854642862750533) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell071.Kernel169
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
  base := (63830601074106234719661251580182362228667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (938492)
      previous := (469246)
      next := (469246)
      square := (3133988453023522318674487492215000000000000)
      linear := (-530980868140178383748060983046085400000000000)
      constant := (23141700771412123402619146456599891042719632067) }

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
  base := (15957650268525362081532705536683521727081/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (469246)
      previous := (234623)
      next := (234623)
      square := (1566994226511761159337243746107500000000000)
      linear := (-266145934130189408794644338535647075000000000)
      constant := (11626448495994308998404053232306275372775906562) }

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
end ForestUnimodality.Stage130KernelData.Cell071.Kernel169
