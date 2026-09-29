import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell137.Parameters
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch000_049
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch050_099
import ForestUnimodality.BinomialMassData.Q4657_8862.Batch000_049
import ForestUnimodality.BinomialMassData.Q4657_8862.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree000.table
  base := (36890943353216129431118019923/1000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (1143846048761689854211809300000000000000)
      linear := (-53179580923002527440002218000000000000)
      constant := (368909433532161294311180199230000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree000.table
  base := (36890943353216129431118019923/1000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (1143846048761689854211809300000000000000)
      linear := (-53179580923002527440002218000000000000)
      constant := (368909433532161294311180199230000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree001.table
  base := (41115619506147674658310855581316295138257/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-8207409170399896377099740343431166000000000000)
      constant := (1347669284082792662053307069739199376249999824295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree001.table
  base := (2567542683812726552009272446346937821/125000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-8215856473470001456673094555111666000000000000)
      constant := (1346530690190924846546384995566540716249994160000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49934921713380101607/100000000000000000000)
  directionHi := (6241865214172512701/12500000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree002.table
  base := (60006743939669854332595888036134498565379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-16066779946825662412148498890968366000000000000)
      constant := (794055473480104767088966016219192011124996106946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree002.table
  base := (119831299263586485589718301164025098394291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-16083674552965872571295207314329366000000000000)
      constant := (792881263736549882132875534127542228624997752817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49934921713380101607/100000000000000000000)
  centralHi := (6241865214172512701/12500000000000000000)
  directionLo := (70618643523100888607/100000000000000000000)
  directionHi := (2206832610096902769/3125000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree003.table
  base := (4623490116176711904263173357394470827801/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-7975383574417142815732419146168522000000000000)
      constant := (167751665696376195667436214251244676808030203664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree003.table
  base := (73829890768959075358699460924904552273521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-7983830877487247895305773357849022000000000000)
      constant := (167446775605434321475297753938513429016701993609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70618643523100888607/100000000000000000000)
  centralHi := (2206832610096902769/3125000000000000000)
  directionLo := (86489821479548670803/100000000000000000000)
  directionHi := (21622455369887167701/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree004.table
  base := (48212852120869454379630460749485222694607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-31785521499677194482246015986042766000000000000)
      constant := (349269454517966276413780112344154589139229942309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree004.table
  base := (48105211360376368091912921506442721098547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-31819310711957614800539432832764766000000000000)
      constant := (348636762744369493524988319060066652746176415089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86489821479548670803/100000000000000000000)
  centralHi := (21622455369887167701/25000000000000000000)
  directionLo := (49934921713380101607/50000000000000000000)
  directionHi := (19973968685352040643/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree005.table
  base := (206280061145082592772516315932148780389/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-39644892276102960517294774533579966000000000000)
      constant := (268487365372042378719488347102096586431952694880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree005.table
  base := (16463359534869503812534555830850145926499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-39687128791453485915161545591982466000000000000)
      constant := (268088193053372008368981313642828507957336621826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49934921713380101607/50000000000000000000)
  centralHi := (19973968685352040643/20000000000000000000)
  directionLo := (22331575880449635399/20000000000000000000)
  directionHi := (27914469850562044249/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree006.table
  base := (11709582219199604706424684520074141188991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-15834754350842908850781177693705722000000000000)
      constant := (76209074792617664319996839282139714307756694478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree006.table
  base := (23361420708788398633790012260244413911811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-15851648956983119009927886117066722000000000000)
      constant := (76136738217448251119895692825681238036619139019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22331575880449635399/20000000000000000000)
  centralHi := (27914469850562044249/25000000000000000000)
  directionLo := (61157539271802780027/50000000000000000000)
  directionHi := (24463015708721112011/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree007.table
  base := (16934472299989482784208779892074469621747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-1129870078141928420150863094462334000000000000)
      constant := (4350759659376438786767996454744090386089394561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree007.table
  base := (16890111769348491784008633482725155291367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-1131076835723372002947056553273834000000000000)
      constant := (4349299478913007394163512956364537916180850621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61157539271802780027/50000000000000000000)
  centralHi := (24463015708721112011/20000000000000000000)
  directionLo := (33028846147770774037/25000000000000000000)
  directionHi := (132115384591083096149/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree008.table
  base := (12245244499624528456545914261426419216069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-63223004605380258622441050176191566000000000000)
      constant := (213623476690309563920669131855151832658035368503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree008.table
  base := (6104815524835452763664168754247209688103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-63290583029941099259027883869635566000000000000)
      constant := (213675920636683000079279976072562574622065896922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33028846147770774037/25000000000000000000)
  centralHi := (132115384591083096149/100000000000000000000)
  directionLo := (70618643523100888607/50000000000000000000)
  directionHi := (28247457409240355443/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree009.table
  base := (1732412028917331069128037427744461583347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-23694125127268674885829936241242922000000000000)
      constant := (75141336502812195775765496259681245667286987815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree009.table
  base := (8632307760010167079361025129991522581321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-23719467036478990124549998876284422000000000000)
      constant := (75196810617111237387310148360210804265306619809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70618643523100888607/50000000000000000000)
  centralHi := (28247457409240355443/20000000000000000000)
  directionLo := (149804765140140304821/100000000000000000000)
  directionHi := (74902382570070152411/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree010.table
  base := (1161970010829474381810142666451176218881/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-78941746158231790692538567271265966000000000000)
      constant := (246134148879530234493245331560002880083988735735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree010.table
  base := (2892113730590484674923291144392550972823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-79026219188932841488272109388070966000000000000)
      constant := (246412092532885047188039372800744733987149518202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149804765140140304821/100000000000000000000)
  centralHi := (74902382570070152411/50000000000000000000)
  directionLo := (157908087396478827161/100000000000000000000)
  directionHi := (78954043698239413581/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree011.table
  base := (868943012492676069133320737923626579911/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-86801116934657556727587325818803166000000000000)
      constant := (274360930650201209194975717324486890030959967028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree011.table
  base := (1726627721069181064064934484747780790387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-86894037268428712602894222147288666000000000000)
      constant := (274752568609183467593305868405066434879232970338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157908087396478827161/100000000000000000000)
  centralHi := (78954043698239413581/50000000000000000000)
  directionLo := (6624615970362103333/4000000000000000000)
  directionHi := (82807699629526291663/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree012.table
  base := (1532218106453445644631518371942638222989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-31553495903694440920878694788780122000000000000)
      constant := (103089737664997032342758494000068195619958970181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree012.table
  base := (1512195732063022030156043955516971648933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-31587285115974861239172111635502122000000000000)
      constant := (103259804994384150069882870260111387644325158557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6624615970362103333/4000000000000000000)
  centralHi := (82807699629526291663/50000000000000000000)
  directionLo := (86489821479548670803/50000000000000000000)
  directionHi := (172979642959097341607/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree013.table
  base := (-51199243495162891403453862760111588969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-102519858487509088797684842913877566000000000000)
      constant := (350325044588426511823029454198621847152568278394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree013.table
  base := (-12030752919419933859567619397093491169/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-102629673427420454832138447665724066000000000000)
      constant := (350960191150086060393216009389940328999107477970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86489821479548670803/50000000000000000000)
  centralHi := (172979642959097341607/100000000000000000000)
  directionLo := (22505365084234009867/12500000000000000000)
  directionHi := (180042920673872078937/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree014.table
  base := (-741909715954734542498104930073575296991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-2252637331917037853729257172681934000000000000)
      constant := (8105379979901896134379190109398262125215982134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree014.table
  base := (-1499870701108434777014830811605966045763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-2255050847079925019321644090304934000000000000)
      constant := (8121039000138286065410652462888058357029756431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22505365084234009867/12500000000000000000)
  centralHi := (180042920673872078937/100000000000000000000)
  directionLo := (186839368686847134703/100000000000000000000)
  directionHi := (11677460542927945919/6250000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree015.table
  base := (-2652492852307587483761169140008102825507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-39412866680120206955927453336317322000000000000)
      constant := (149840073336253974571405162256054443451174539797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree015.table
  base := (-533375076675834598006888950132294646463/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-39455103195470732353794224394719822000000000000)
      constant := (150142431220263280986804994776549356960981090365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186839368686847134703/100000000000000000000)
  centralHi := (11677460542927945919/6250000000000000000)
  directionLo := (38679424038018452963/20000000000000000000)
  directionHi := (12087320011880766551/6250000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree016.table
  base := (-363923088726252381470947523005109106707/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-126097970816786386902831118556489166000000000000)
      constant := (507193194844282509001973745540314196066637549910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree016.table
  base := (-3652098608011335065978416546542183682041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-126233127665908068176004785943377166000000000000)
      constant := (508247916148569547168424612190211145722902337933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38679424038018452963/20000000000000000000)
  centralHi := (12087320011880766551/6250000000000000000)
  directionLo := (49934921713380101607/25000000000000000000)
  directionHi := (199739686853520406429/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree017.table
  base := (-4468355995640218583359876881456115795773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-133957341593212152937879877104026366000000000000)
      constant := (570023363073652597472663660343728575492489369249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree017.table
  base := (-559980463283082474341143950440757813157/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-134100945745403939290626898702594866000000000000)
      constant := (571233723204295949721490732325636769166914150728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49934921713380101607/25000000000000000000)
  centralHi := (199739686853520406429/100000000000000000000)
  directionLo := (205886956631214965899/100000000000000000000)
  directionHi := (2058869566312149659/1000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree018.table
  base := (-80617804623067118425207483019585775563/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-47272237456545972990976211883854522000000000000)
      constant := (212627328013988515112208957670514444007796747072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree018.table
  base := (-5169770487383260060201718609782574949069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-47322921274966603468416337153937522000000000000)
      constant := (213085349831989183204336759031741335053932453499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205886956631214965899/100000000000000000000)
  centralHi := (2058869566312149659/1000000000000000000)
  directionLo := (211855930569302665821/100000000000000000000)
  directionHi := (105927965284651332911/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree019.table
  base := (-2864471683923313027326956663909681930491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-149676083146063685007977394199100766000000000000)
      constant := (710663284265831463981835819776023536927147395566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree019.table
  base := (-1147606542695361563655933249905658537173/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-149836581904395681519871124221030266000000000000)
      constant := (712209175322080295186243200266381973555892837245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211855930569302665821/100000000000000000000)
  centralHi := (105927965284651332911/50000000000000000000)
  directionLo := (43532255500447753071/20000000000000000000)
  directionHi := (54415319375559691339/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree020.table
  base := (-6189978109117360625646214802181154187747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-157535453922489451043026152746637966000000000000)
      constant := (788279497577215392447007668987546366657875424511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree020.table
  base := (-774754231479941134638149692754874900919/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-157704399983891552634493236980247966000000000000)
      constant := (790005380524825469733240145807797632294553796376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43532255500447753071/20000000000000000000)
  centralHi := (54415319375559691339/25000000000000000000)
  directionLo := (223315758804496353991/100000000000000000000)
  directionHi := (27914469850562044249/12500000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree021.table
  base := (-819229863734033419972223848848873761657/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3294554)
      previous := (1647277)
      next := (1647277)
      square := (50925169936919193999363961845300000000000000)
      linear := (-1125134861897382429102550416967178000000000000)
      constant := (5922839157006653840993152677133342330058149624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree021.table
  base := (-3280481163599288375403903205095840762099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3294554)
      previous := (1647277)
      next := (1647277)
      square := (50925169936919193999363961845300000000000000)
      linear := (-1126341619478826011898743875778678000000000000)
      constant := (5935860146157709317994402118879124146861180842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223315758804496353991/100000000000000000000)
  centralHi := (27914469850562044249/12500000000000000000)
  directionLo := (228830558573258284107/100000000000000000000)
  directionHi := (57207639643314571027/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree022.table
  base := (-170747652255735999465962078085316833687/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-173254195475340983113123669841712366000000000000)
      constant := (957735469453018915883694645258060014374835909240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree022.table
  base := (-6836191635587254539952776155726001216439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-173440036142883294863737462498683366000000000000)
      constant := (959846012542869584256282651520800358876909134307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228830558573258284107/100000000000000000000)
  centralHi := (57207639643314571027/25000000000000000000)
  directionLo := (117107771884993600039/50000000000000000000)
  directionHi := (234215543769987200079/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree023.table
  base := (-3513028379628747807772659899056725622003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-181113566251766749148172428389249566000000000000)
      constant := (1049462285270729742421427385831135510463344504478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree023.table
  base := (-3515795981656335393838174139771157360677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-181307854222379165978359575257901066000000000000)
      constant := (1051777586578891333996475780588851999124717989202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117107771884993600039/50000000000000000000)
  centralHi := (234215543769987200079/100000000000000000000)
  directionLo := (47895894333436217599/20000000000000000000)
  directionHi := (59869867916795271999/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree024.table
  base := (-7148914501590028118199822963257209861543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-62990979009397505061073728978928922000000000000)
      constant := (381931484969074725393414767841811150227957960753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree024.table
  base := (-1788444987797831059448275278264600786081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-63058557433958345697660562672372922000000000000)
      constant := (382774286803925730633823759640369222846966008604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47895894333436217599/20000000000000000000)
  centralHi := (59869867916795271999/25000000000000000000)
  directionLo := (61157539271802780027/25000000000000000000)
  directionHi := (244630157087211120109/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree025.table
  base := (-900506660043087321061918227643996405369/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-196832307804618281218269945484323966000000000000)
      constant := (1246695499075943892973180223586720383979002499176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree025.table
  base := (-7208322709681015537894640327476716304053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-197043490381370908207603800776336466000000000000)
      constant := (1249445399602797471804449542732689539673806688889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61157539271802780027/25000000000000000000)
  centralHi := (244630157087211120109/100000000000000000000)
  directionLo := (49934921713380101607/20000000000000000000)
  directionHi := (62418652141725127009/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree026.table
  base := (-7196165989403045171649350373489664732013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-204691678581044047253318704031861166000000000000)
      constant := (1352134704724599398322365612025729331560509236369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree026.table
  base := (-3599953239624316118886806148692725284237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-204911308460866779322225913535554166000000000000)
      constant := (1355114534643513707516575765864870572220422449762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49934921713380101607/20000000000000000000)
  centralHi := (62418652141725127009/25000000000000000000)
  directionLo := (1591369626414082471/625000000000000000)
  directionHi := (254619140226253195361/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree027.table
  base := (-222787651181172090269852129316973036831/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-70850349785823271096122487526466122000000000000)
      constant := (487362068759111903208506747195066464093923372832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree027.table
  base := (-3566238551544270504119313768759562110353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-70926375513454216812282675431590622000000000000)
      constant := (488434813873284002816947545484951976457927460526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1591369626414082471/625000000000000000)
  centralHi := (254619140226253195361/100000000000000000000)
  directionLo := (259469464438646012409/100000000000000000000)
  directionHi := (25946946443864601241/10000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree028.table
  base := (-7006498812060083088860579245763707636557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-4498171839467256720886045329121134000000000000)
      constant := (32174045242697394463787994287741053916938537409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree028.table
  base := (-700935755391237024490004330745624341099/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-4502998869793031052070819164367134000000000000)
      constant := (32244762715261275442051178639107193761297942630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259469464438646012409/100000000000000000000)
  centralHi := (25946946443864601241/10000000000000000000)
  directionLo := (33028846147770774037/12500000000000000000)
  directionHi := (264230769182166192297/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree029.table
  base := (-3415426116171237209796451425305179368723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-228269790910321345358464979674472766000000000000)
      constant := (1695442383451900597538640801730151748141574495198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree029.table
  base := (-1366669306362943518462894133614830607937/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-228514762699354392666092251813207266000000000000)
      constant := (1699163012591109169630775298935986186980467064905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33028846147770774037/12500000000000000000)
  centralHi := (264230769182166192297/100000000000000000000)
  directionLo := (134453891528955556229/50000000000000000000)
  directionHi := (268907783057911112459/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree030.table
  base := (-3302313791608746533747300982449981581671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-78709720562249037131171246074003322000000000000)
      constant := (606271081490232529624778470706228108260237690082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree030.table
  base := (-6606801317454294882369757486348600990463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-78794193592950087926904788190808322000000000000)
      constant := (607599310940472556823308626235289932829876242073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134453891528955556229/50000000000000000000)
  centralHi := (268907783057911112459/100000000000000000000)
  directionLo := (17094051893545500433/6250000000000000000)
  directionHi := (273504830296728006929/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree031.table
  base := (-6329815197632710320688896486896130347139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-243988532463172877428562496769547166000000000000)
      constant := (1946627774041428955998871071920592030979808613407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree031.table
  base := (-633170746290027250022215315418245257523/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-244250398858346134895336477331642666000000000000)
      constant := (1950885139120468283574480909886897931248033219990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17094051893545500433/6250000000000000000)
  centralHi := (273504830296728006929/100000000000000000000)
  directionLo := (278025877576464787989/100000000000000000000)
  directionHi := (27802587757646478799/10000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree032.table
  base := (-6008091915542700646709434307209248951321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-251847903239598643463611255317084366000000000000)
      constant := (2078874997939126910261495147088408695033420950573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree032.table
  base := (-3004868722681453178718212746681156618301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-252118216937842006009958590090860366000000000000)
      constant := (2083413685815652971838940463334587650501806626626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278025877576464787989/100000000000000000000)
  centralHi := (27802587757646478799/10000000000000000000)
  directionLo := (70618643523100888607/25000000000000000000)
  directionHi := (282474574092403554429/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree033.table
  base := (-5640870479138243507508119124701210236999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-86569091338674803166220004621540522000000000000)
      constant := (738515223449871774958550071349770289532889808529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree033.table
  base := (-2821150024468575512659635833892832703231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-86662011672445959041526900950026022000000000000)
      constant := (740124784332299362936780051925719541131506359602) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70618643523100888607/25000000000000000000)
  centralHi := (282474574092403554429/100000000000000000000)
  directionLo := (2868542860324840691/1000000000000000000)
  directionHi := (286854286032484069101/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree034.table
  base := (-2614670568167707543687617892788239811507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-267566644792450175533708772412158766000000000000)
      constant := (2356632001591855870554620470372531807953457674782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree034.table
  base := (-5230581948671659115282681507877375394699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-267853853096833748239202815609295766000000000000)
      constant := (2361759374366106998240517026926280065397733055687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2868542860324840691/1000000000000000000)
  centralHi := (286854286032484069101/100000000000000000000)
  directionLo := (72792031595896360361/25000000000000000000)
  directionHi := (58233625276717088289/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree035.table
  base := (-4774506686018794276796942824904630140839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-5620939093242366154464439407340734000000000000)
      constant := (51063825076761324852882771004684002884499120643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree035.table
  base := (-2387791366284423210825234340171097369889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-5626972881149584068445406701398234000000000000)
      constant := (51174738939441504770476423919763545443971030986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72792031595896360361/25000000000000000000)
  centralHi := (58233625276717088289/20000000000000000000)
  directionLo := (147709490409595029499/50000000000000000000)
  directionHi := (295418980819190058999/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree036.table
  base := (-4277212001068054983949015543654624890151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-94428462115100569201268763169077722000000000000)
      constant := (884008807504632500053956589290207101818013779121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree036.table
  base := (-4278144399183016446408399464101092190469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-94529829751941830156149013709243722000000000000)
      constant := (885925781154561927285224290343165020454818352899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147709490409595029499/50000000000000000000)
  centralHi := (295418980819190058999/100000000000000000000)
  directionLo := (149804765140140304821/50000000000000000000)
  directionHi := (299609530280280609643/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree037.table
  base := (-1869084450215844907475453874873829708587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-291144757121727473638855048054770366000000000000)
      constant := (2806324324288596959286856938457425746897935462862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree037.table
  base := (-3738976203320198456794993390213506683767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-291457307335321361583069153886948866000000000000)
      constant := (2812400138879479915883512582987306368933005380771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149804765140140304821/50000000000000000000)
  centralHi := (299609530280280609643/100000000000000000000)
  directionLo := (151871135375761729263/50000000000000000000)
  directionHi := (303742270751523458527/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree038.table
  base := (-1578988551748392207801216541743281684559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-299004127898153239673903806602307566000000000000)
      constant := (2965017209169698926480829226037180890699794135734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree038.table
  base := (-3158675584004341840295206989899719090449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-299325125414817232697691266646166566000000000000)
      constant := (2971426684288346703986871898732058305136995650437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151871135375761729263/50000000000000000000)
  centralHi := (303742270751523458527/100000000000000000000)
  directionLo := (307819530647119892279/100000000000000000000)
  directionHi := (7695488266177997307/2500000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree039.table
  base := (-1268570942063146169601573756451948385947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-102287832891526335236317521716614922000000000000)
      constant := (1042700590116149492045752849838576142979106854074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree039.table
  base := (-2537745792738390929423122031574799713491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-102397647831437701270771126468461422000000000000)
      constant := (1044951228705680748741818493801748196755827692261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307819530647119892279/100000000000000000000)
  centralHi := (7695488266177997307/2500000000000000000)
  directionLo := (19490217884389965473/6250000000000000000)
  directionHi := (311843486150239447569/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree040.table
  base := (-1876088944308114973643215780550292753083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-314722869451004771744001323697381966000000000000)
      constant := (3295575221781149714675676979291113141201978788279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree040.table
  base := (-938305371229335485206320976280250552537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-315060761573808974926935492164601966000000000000)
      constant := (3302678370030474336564989127611713967754247065562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19490217884389965473/6250000000000000000)
  centralHi := (311843486150239447569/100000000000000000000)
  directionLo := (315816174792957654323/100000000000000000000)
  directionHi := (78954043698239413581/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree041.table
  base := (-587588472688615607146140712780312970473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-322582240227430537779050082244919166000000000000)
      constant := (3467435216177492336572173986062478935755022040698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree041.table
  base := (-587813757720518645077938440982732587497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-322928579653304846041557604923819666000000000000)
      constant := (3474898399072622481819213982997933698166781542522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315816174792957654323/100000000000000000000)
  centralHi := (78954043698239413581/25000000000000000000)
  directionLo := (319739507517255961067/100000000000000000000)
  directionHi := (79934876879313990267/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree042.table
  base := (-108677016437635015759654115828186618169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3294554)
      previous := (1647277)
      next := (1647277)
      square := (50925169936919193999363961845300000000000000)
      linear := (-2247902115672491862680944495186778000000000000)
      constant := (24786937251051274993460398703030749214289991804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree042.table
  base := (-108774224819017543497020826387203029123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3294554)
      previous := (1647277)
      next := (1647277)
      square := (50925169936919193999363961845300000000000000)
      linear := (-2250315630835379028273331412809778000000000000)
      constant := (24840216358591371489321555355956047335761659668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319739507517255961067/100000000000000000000)
  centralHi := (79934876879313990267/25000000000000000000)
  directionLo := (323615279419712784331/100000000000000000000)
  directionHi := (80903819854928196083/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree043.table
  base := (172531552006250452387734767372183751681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-338300981780282069849147599339993566000000000000)
      constant := (3824307234772219228300554049368956183885725401494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree043.table
  base := (43090967273213089308433020568262931467/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-338664215812296588270801830442255066000000000000)
      constant := (3832516928763460949696837834670466307550886553032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323615279419712784331/100000000000000000000)
  centralHi := (80903819854928196083/25000000000000000000)
  directionLo := (65489035870264628693/20000000000000000000)
  directionHi := (163722589675661571733/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree044.table
  base := (1163922066970368599089784118287255901979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-346160352556707835884196357887530766000000000000)
      constant := (4009316188986642717582392541404902021241765037673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree044.table
  base := (232726594608737831236116833551153364007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-346532033891792459385423943201472766000000000000)
      constant := (4017912374452925159722433497492729454705432400545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65489035870264628693/20000000000000000000)
  centralHi := (163722589675661571733/50000000000000000000)
  directionLo := (6624615970362103333/2000000000000000000)
  directionHi := (331230798518105166651/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree045.table
  base := (40433762115427602363639767724549854757/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-118006574444377867306415038811689322000000000000)
      constant := (1399568485275792464512486596223900016004909172650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree045.table
  base := (1010719514064107508587689635166008385817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-118133283990429443500015351986896822000000000000)
      constant := (1402565655071332244047707569711362274215805948386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6624615970362103333/2000000000000000000)
  centralHi := (331230798518105166651/100000000000000000000)
  directionLo := (334973638206744530987/100000000000000000000)
  directionHi := (83743409551686132747/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree046.table
  base := (2918208962972399711704221849905615906379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-361879094109559367954293874982605166000000000000)
      constant := (4392474038832340256694793937937455901087881220473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree046.table
  base := (2917994468546999812115872580781234588231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-362267670050784201614668168719908166000000000000)
      constant := (4401869709967848288605047944598168863730086955597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334973638206744530987/100000000000000000000)
  centralHi := (83743409551686132747/25000000000000000000)
  directionLo := (169337558370835425061/50000000000000000000)
  directionHi := (338675116741670850123/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree047.table
  base := (1926678179555771257456418049242558482863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-369738464885985133989342633530142366000000000000)
      constant := (4590621098465432688373096949480038308187369825162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree047.table
  base := (192658586674265074194878301511419709071/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-370135488130280072729290281479125866000000000000)
      constant := (4600429773881629958832929848181890977590596973540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169337558370835425061/50000000000000000000)
  centralHi := (338675116741670850123/100000000000000000000)
  directionLo := (342336575765000282113/100000000000000000000)
  directionHi := (171168287882500141057/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree048.table
  base := (1206755554150829275425987763488236426693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-125865945220803633341463797359226522000000000000)
      constant := (1597715309134497896665492636363774691694748614388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree048.table
  base := (2413431686211482823267218568737689763313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-126001102069925314614637464746114522000000000000)
      constant := (1601125484578688132398083771657698743223340891154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342336575765000282113/100000000000000000000)
  centralHi := (171168287882500141057/50000000000000000000)
  directionLo := (86489821479548670803/25000000000000000000)
  directionHi := (345959285918194683213/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree049.table
  base := (1459778869575452829543983961321663675301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-7866473600792585021621227563779934000000000000)
      constant := (102041794483981834036313677634571857461856909852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree049.table
  base := (729872359339512551373640616170052338397/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-7874920903862690101194581775460434000000000000)
      constant := (102259370554619759738828836527194341603786548088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86489821479548670803/25000000000000000000)
  centralHi := (345959285918194683213/100000000000000000000)
  directionLo := (349544451993660711249/100000000000000000000)
  directionHi := (279635561594928569/80000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree050.table
  base := (3444779713541237191085556554056857957003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-393316577215262432094488909172753966000000000000)
      constant := (5211326603318385209292024867259062419692496785522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree050.table
  base := (6889441998998768520690971560732375401801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-393738942368767686073156619756778966000000000000)
      constant := (5222427385234289073645846880845346364533746601187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349544451993660711249/100000000000000000000)
  centralHi := (279635561594928569/80000000000000000)
  directionLo := (70618643523100888607/20000000000000000000)
  directionHi := (88273304403876110759/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree051.table
  base := (1595657885508239016292178727810867757791/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-133725315997229399376512555906763722000000000000)
      constant := (1808993841733764742849445477552556184643930212195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree051.table
  base := (7978188523607553416522037343444934574879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-133868920149421185729259577505332222000000000000)
      constant := (1812843572535187807378521662820580226678201209991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70618643523100888607/20000000000000000000)
  centralHi := (88273304403876110759/25000000000000000000)
  directionLo := (178303334750497148869/50000000000000000000)
  directionHi := (356606669500994297739/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree052.table
  base := (364210040933396621327828593405027874153/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-409035318768113964164586426267828366000000000000)
      constant := (5647012338969562081387960129922671850995483995275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree052.table
  base := (9105164351654328224105596648210374609287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-409474578527759428302400845275214366000000000000)
      constant := (5659018800248400497075370761025702442933069779469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178303334750497148869/50000000000000000000)
  centralHi := (356606669500994297739/100000000000000000000)
  directionLo := (360085841347744157873/100000000000000000000)
  directionHi := (180042920673872078937/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree053.table
  base := (10270398334156744361032072672998010913869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-416894689544539730199635184815365566000000000000)
      constant := (5871418744355528730498866155088540541252765177103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree053.table
  base := (5135161957418297551378958435504189945983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-417342396607255299417022958034432066000000000000)
      constant := (5883891334937080159029597371025484147932022088042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360085841347744157873/100000000000000000000)
  centralHi := (180042920673872078937/50000000000000000000)
  directionLo := (363531717386026959231/100000000000000000000)
  directionHi := (2840091542078335619/781250000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree054.table
  base := (2868423176289654106902676972586126237433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-141584686773655165411561314454300922000000000000)
      constant := (2033400162793059347269313295219140405538483900228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree054.table
  base := (11473628828889126989218642011315278100127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-141736738228917056843881690264549922000000000000)
      constant := (2037716023487479732802660971654895525318491954183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363531717386026959231/100000000000000000000)
  centralHi := (2840091542078335619/781250000000000000)
  directionLo := (366945235630816680163/100000000000000000000)
  directionHi := (91736308907704170041/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree055.table
  base := (6357550784532812342403697498821334639173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-432613431097391262269732701910439966000000000000)
      constant := (6333357357901146033221819141105516224004362613102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree055.table
  base := (794690422562838274882723428500037248131/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-433078032766247041646267183552867466000000000000)
      constant := (6346788795219612446628062177496819802378142670352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366945235630816680163/100000000000000000000)
  centralHi := (91736308907704170041/25000000000000000000)
  directionLo := (46290911358001234881/12500000000000000000)
  directionHi := (370327290864009879049/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree056.table
  base := (6997298743743484295461970764760369541683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-8989240854567694455199621641999534000000000000)
      constant := (134099779047928509603994142308172562474191613058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree056.table
  base := (2798910095162330019703310660135717772223/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-8998894915219243117569169312491534000000000000)
      constant := (134383945529884216000268070664155678364057102745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46290911358001234881/12500000000000000000)
  centralHi := (370327290864009879049/100000000000000000000)
  directionLo := (186839368686847134703/50000000000000000000)
  directionHi := (373678737373694269407/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree057.table
  base := (957009833950207399310883470522117521791/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-149444057550080931446610073001838122000000000000)
      constant := (2270931927809525917417778753228374396243123175024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree057.table
  base := (765605851587214956932860499315264289177/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-149604556308412927958503803023767622000000000000)
      constant := (2275740509184507700258825044837296127790080232660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186839368686847134703/50000000000000000000)
  centralHi := (373678737373694269407/100000000000000000000)
  directionLo := (94250097868556539073/25000000000000000000)
  directionHi := (377000391474226156293/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree058.table
  base := (16667761659654556994576924495780944521063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-456191543426668560374878977553051566000000000000)
      constant := (7059077060675346231205770861632427212360270135981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree058.table
  base := (16667727104119903045006727680021426612137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-456681487004734654990133521830520566000000000000)
      constant := (7074013258515129868566293206144053546327245852419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94250097868556539073/25000000000000000000)
  centralHi := (377000391474226156293/100000000000000000000)
  directionLo := (380293033828179889073/100000000000000000000)
  directionHi := (190146516914089944537/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree059.table
  base := (18061394027596150208210611473975861331223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-464050914203094326409927736100588766000000000000)
      constant := (7309732897697073949109771674814239584382124739901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree059.table
  base := (4515341103731002844462971732421054194099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-464549305084230526104755634589738266000000000000)
      constant := (7325188417316265129222698257685482873219983168452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380293033828179889073/100000000000000000000)
  centralHi := (190146516914089944537/50000000000000000000)
  directionLo := (383557411588881401709/100000000000000000000)
  directionHi := (38355741158888140171/10000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree060.table
  base := (19493040622047028638280425747174896892077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-157303428326506697481658831549375322000000000000)
      constant := (2521587734671656507993003217845397425642075845733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree060.table
  base := (9746507626247405567984524434477747664673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-157472374387908799073125915782985322000000000000)
      constant := (2526915638073255077660483692706281632770332850034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383557411588881401709/100000000000000000000)
  centralHi := (38355741158888140171/10000000000000000000)
  directionLo := (38679424038018452963/10000000000000000000)
  directionHi := (386794240380184529631/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree061.table
  base := (20962689795309701059557075215752382094117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-479769655755945858480025253195663166000000000000)
      constant := (7824167903399663374808235100703872431072190894679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree061.table
  base := (5240667016732365182874308154169521488211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-480284941243222268333999860108173666000000000000)
      constant := (7840688673636286191523577334162069820511865455428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38679424038018452963/10000000000000000000)
  centralHi := (386794240380184529631/100000000000000000000)
  directionLo := (390004206128351097919/100000000000000000000)
  directionHi := (1218763144151097181/312500000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree062.table
  base := (22470331734082595148595545227588654075581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-487629026532371624515074011743200366000000000000)
      constant := (8087946931627149604289869978210208178810544430047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree062.table
  base := (5617578282318837413144059594719621687041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-488152759322718139448621972867391366000000000000)
      constant := (8105013631893851226477093416426115980951706388268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390004206128351097919/100000000000000000000)
  centralHi := (1218763144151097181/312500000000000000)
  directionLo := (24574247922457392097/6250000000000000000)
  directionHi := (393187966759318273553/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree063.table
  base := (12007979085285626542998866034454617332971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3294554)
      previous := (1647277)
      next := (1647277)
      square := (50925169936919193999363961845300000000000000)
      linear := (-3370669369447601296259338573406378000000000000)
      constant := (56844219282912435953109068766431152036562403782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree063.table
  base := (24015942244450509110753775690745916918031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3294554)
      previous := (1647277)
      next := (1647277)
      square := (50925169936919193999363961845300000000000000)
      linear := (-3374289642191932044647918949840878000000000000)
      constant := (56964093437816553884181555881733052967107658151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24574247922457392097/6250000000000000000)
  centralHi := (393187966759318273553/100000000000000000000)
  directionLo := (99086538443312322111/25000000000000000000)
  directionHi := (79269230754649857689/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree064.table
  base := (6399890534773632846497540939617970011361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-503347768085223156585171528838274766000000000000)
      constant := (8628627766695092559457596742396083710010972211628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree064.table
  base := (25599548509422701958912665427724642357939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-503888395481709881677866198385826766000000000000)
      constant := (8646812938854337735202423050752759397955416926193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99086538443312322111/25000000000000000000)
  centralHi := (79269230754649857689/20000000000000000000)
  directionLo := (49934921713380101607/12500000000000000000)
  directionHi := (399479373707040812857/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree065.table
  base := (5444227554204231153938877117362721018187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-511207138861648922620220287385811966000000000000)
      constant := (8905529489540275081902578570130681031301267018845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree065.table
  base := (5444225221902419760441346545620197762923/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-511756213561205752792488311145044466000000000000)
      constant := (8924287204325086148540568281840419706083274739005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49934921713380101607/12500000000000000000)
  centralHi := (399479373707040812857/100000000000000000000)
  directionLo := (50323526186797526621/12500000000000000000)
  directionHi := (402588209494380212969/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree066.table
  base := (14440340061000141882458186983836117006123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-173022169879358229551756348644449722000000000000)
      constant := (3062268456921647135119803241209608832992501004134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree066.table
  base := (28880670146807302264677978916575481347549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-173208010546900541302370141301420722000000000000)
      constant := (3068714833238823800856865192400452515248637222421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50323526186797526621/12500000000000000000)
  centralHi := (402588209494380212969/100000000000000000000)
  directionLo := (405673221731990056917/100000000000000000000)
  directionHi := (202836610865995028459/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree067.table
  base := (6115637005280068554337597759101015894831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-526925880414500454690317804480886366000000000000)
      constant := (9472455383106753293000782512741606813560521648985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree067.table
  base := (7644544123908000504776007086981428297243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-527491849720197495021732536663479866000000000000)
      constant := (9492384798027645950516999631078733741502274694564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405673221731990056917/100000000000000000000)
  centralHi := (202836610865995028459/50000000000000000000)
  directionLo := (408734949859849603413/100000000000000000000)
  directionHi := (204367474929924801707/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree068.table
  base := (32313648974671321964129458449647611212177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-534785251190926220725366563028423566000000000000)
      constant := (9762479503597155368125784920557451958920267835899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree068.table
  base := (32313641680797686339466536593877901450959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-535359667799693366136354649422697566000000000000)
      constant := (9783008076514936235988333224765745261423227408933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408734949859849603413/100000000000000000000)
  centralHi := (204367474929924801707/50000000000000000000)
  directionLo := (411773913262429931799/100000000000000000000)
  directionHi := (2058869566312149659/500000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree069.table
  base := (17043534505010239142701319622134823378351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-180881540655783995586805107191986922000000000000)
      constant := (3352292570961720094276764590268648546219501357358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree069.table
  base := (34087062775050151072487538027301915895803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-181075828626396412416992254060638422000000000000)
      constant := (3359338105340224149595902459010876469282255222787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411773913262429931799/100000000000000000000)
  centralHi := (2058869566312149659/500000000000000000)
  directionLo := (16591624491892362903/4000000000000000000)
  directionHi := (6481103317145454259/1562500000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree070.table
  base := (35898442641359932882184101875703295382769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-11234775362117913322356409798438734000000000000)
      constant := (211339795809543401822719870230018039241208775947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree070.table
  base := (35898437312683870934101362536086120789563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-11246842937932349150318344386553734000000000000)
      constant := (211783744906282250251282746859538200551016402969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16591624491892362903/4000000000000000000)
  centralHi := (6481103317145454259/1562500000000000000)
  directionLo := (417785529256935810357/100000000000000000000)
  directionHi := (208892764628467905179/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree071.table
  base := (37747767769963619521285921576254697535363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-558363363520203518830512838671035166000000000000)
      constant := (10658796335209259257943863870960639558178868730081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree071.table
  base := (1509910528671013620268240466913557040869/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-558963122038180979480220987700350666000000000000)
      constant := (10681175616083803103013307271807153334335743152575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417785529256935810357/100000000000000000000)
  centralHi := (208892764628467905179/50000000000000000000)
  directionLo := (420759129268776968633/100000000000000000000)
  directionHi := (210379564634388484317/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree072.table
  base := (39635042627674600300130758616542529448437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-188740911432209761621853865739524122000000000000)
      constant := (3655438907646067026321683178595906671725119320173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree072.table
  base := (39635038737888328553338436014411025324531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-188943646705892283531614366819856122000000000000)
      constant := (3663110217199751118202214370455624493665198787899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420759129268776968633/100000000000000000000)
  centralHi := (210379564634388484317/50000000000000000000)
  directionLo := (211855930569302665821/50000000000000000000)
  directionHi := (423711861138605331643/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree073.table
  base := (8312053144968753073294812811019595675981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-574082105073055050900610355766109566000000000000)
      constant := (11278211148105313953476259039928924741031407324235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree073.table
  base := (41560262402442475602486812894585302168827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-574698758197172721709465213218786066000000000000)
      constant := (11301868597310206153040278969828902386965176989449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211855930569302665821/50000000000000000000)
  centralHi := (423711861138605331643/100000000000000000000)
  directionLo := (106661039535314324687/25000000000000000000)
  directionHi := (426644158141257298749/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree074.table
  base := (43523435806467390730523081841234541737197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-581941475849480816935659114313646766000000000000)
      constant := (11594479602497116824502306579440759509804216902639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree074.table
  base := (5440429121152723545030202795297733634561/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-582566576276668592824087325978003766000000000000)
      constant := (11618789445093415444410807423745816443393685370456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106661039535314324687/25000000000000000000)
  centralHi := (426644158141257298749/100000000000000000000)
  directionLo := (214778219381402572269/50000000000000000000)
  directionHi := (429556438762805144539/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree075.table
  base := (9104910363046474757426290045002168944579/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-196600282208635527656902624287061322000000000000)
      constant := (3971707359731310701934628380705753583077492406455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree075.table
  base := (182098197570959032233379666629538150579/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-196811464785388154646236479579073822000000000000)
      constant := (3980031062702201271586033831852705583023613822750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214778219381402572269/50000000000000000000)
  centralHi := (429556438762805144539/100000000000000000000)
  directionLo := (86489821479548670803/20000000000000000000)
  directionHi := (13514034606179479813/3125000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree076.table
  base := (47563612860381304153640487052680157377423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-597660217402332349005756631408721166000000000000)
      constant := (12240138572366120429236981691297885609130236659301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree076.table
  base := (5945451349047517470590927702737316886071/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-598302212435660335053331551496439166000000000000)
      constant := (12265779820586501635510924730513918144059685981416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86489821479548670803/20000000000000000000)
  centralHi := (13514034606179479813/3125000000000000000)
  directionLo := (435322555004477530711/100000000000000000000)
  directionHi := (54415319375559691339/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree077.table
  base := (9928123638296168672557510565868074096797/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-12357542615893022755934803876658334000000000000)
      constant := (256521001573518480071472433284869615902952488555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree077.table
  base := (49640616426402845205246698768162349544449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-12370816949288902166692931923584834000000000000)
      constant := (257058149748545436072887185500773815892205241787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435322555004477530711/100000000000000000000)
  centralHi := (54415319375559691339/12500000000000000000)
  directionLo := (54772144965265499673/12500000000000000000)
  directionHi := (87635431944424799477/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree078.table
  base := (51755567176321223717792134282185377467799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-204459652985061293691951382834598522000000000000)
      constant := (4301097863088411853886006024026967720321950084671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree078.table
  base := (12938891417511987738551534490578772876333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-204679282864884025760858592338291522000000000000)
      constant := (4310100578431494112655644690667993005256535412628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54772144965265499673/12500000000000000000)
  centralHi := (87635431944424799477/20000000000000000000)
  directionLo := (220506643725687528491/50000000000000000000)
  directionHi := (441013287451375056983/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree079.table
  base := (10781691856459256588839505649412361120307/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-621238329731609647110902907051332766000000000000)
      constant := (13241432105368923177963288443073784525136333141045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree079.table
  base := (6738557249636467804032783393438184151649/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-621905666674147948397197889774092266000000000000)
      constant := (13269137009989852665169628922153972056419904591704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220506643725687528491/50000000000000000000)
  centralHi := (441013287451375056983/100000000000000000000)
  directionLo := (17753251696078239913/4000000000000000000)
  directionHi := (221915646200977998913/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree080.table
  base := (56099294060715906790072287000895908121201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-629097700508035413145951665598869966000000000000)
      constant := (13583944622476976883656255066277647228643206488987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree080.table
  base := (56099292964310569761005849540519502990427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-629773484753643819511820002533309966000000000000)
      constant := (13612355158864121612092767968256551992517609668649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17753251696078239913/4000000000000000000)
  centralHi := (221915646200977998913/50000000000000000000)
  directionLo := (446631517608992707983/100000000000000000000)
  directionHi := (27914469850562044249/6250000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree081.table
  base := (58328071133589072336649598145587279323903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-212319023761487059727000141382135722000000000000)
      constant := (4643610379371867181342018201746814843876194787687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree081.table
  base := (3645504387399630591325154942004231370193/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-212547100944379896875480705097509222000000000000)
      constant := (4653318726491375719278872982132641933708572241552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446631517608992707983/100000000000000000000)
  centralHi := (27914469850562044249/6250000000000000000)
  directionLo := (449414295420420914463/100000000000000000000)
  directionHi := (14044196731888153577/3125000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree082.table
  base := (12118958036497682287960894301172167464207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-644816442060886945216049182693944366000000000000)
      constant := (14282091650200821545072432522885943411740360487545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree082.table
  base := (12118957876984347551185534375064455213549/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-645509120912635561741064228051745366000000000000)
      constant := (14311940069762116568174050979481542570763375046315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449414295420420914463/100000000000000000000)
  centralHi := (14044196731888153577/3125000000000000000)
  directionLo := (452179947957397556327/100000000000000000000)
  directionHi := (56522493494674694541/12500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree083.table
  base := (31449725469584243614810136282559782810949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-652675812837312711251097941241481566000000000000)
      constant := (14637726156977081287847211721873071750614720566126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree083.table
  base := (15724862564769289816334944338864037180869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-653376938992131432855686340810963066000000000000)
      constant := (14668306827994976166298772338965954748005727624412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452179947957397556327/100000000000000000000)
  centralHi := (56522493494674694541/12500000000000000000)
  directionLo := (113732196887379961161/25000000000000000000)
  directionHi := (90985757509903968929/20000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree084.table
  base := (8155256647207700076808534985922594715159/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3294554)
      previous := (1647277)
      next := (1647277)
      square := (50925169936919193999363961845300000000000000)
      linear := (-4493436623222710729837732651625978000000000000)
      constant := (102025405829697384397655830360988270714508750712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree084.table
  base := (65242052597826595394115165439081816657373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3294554)
      previous := (1647277)
      next := (1647277)
      square := (50925169936919193999363961845300000000000000)
      linear := (-4498263653548485061022506486871978000000000000)
      constant := (102238479270156749082630542412789533559402903333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113732196887379961161/25000000000000000000)
  centralHi := (90985757509903968929/20000000000000000000)
  directionLo := (228830558573258284107/50000000000000000000)
  directionHi := (91532223429303313643/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree085.table
  base := (67622596707618437887260142791673083399413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-668394554390164243321195458336555966000000000000)
      constant := (15362117148920366556950686318744429429865714127431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree085.table
  base := (1690564905333260819363864288282515043881/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-669112575151123175084930566329398466000000000000)
      constant := (15394188942686981722986532339646528471339520885880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228830558573258284107/50000000000000000000)
  centralHi := (91532223429303313643/20000000000000000000)
  directionLo := (460377230707947763401/100000000000000000000)
  directionHi := (230188615353973881701/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree086.table
  base := (35020540684348757561117937299456564701051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-676253925166590009356244216884093166000000000000)
      constant := (15730873631792265648071811714970430176814314521874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree086.table
  base := (1094391889803023410339802999840358038139/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-676980393230619046199552679088616166000000000000)
      constant := (15763704296881472916191369101105612980672000229952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460377230707947763401/100000000000000000000)
  centralHi := (230188615353973881701/50000000000000000000)
  directionLo := (231538706786165863651/50000000000000000000)
  directionHi := (463077413572331727303/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree087.table
  base := (3624875351291912438158560369835148601641/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-228037765314338591797097658477210122000000000000)
      constant := (5368001368232432346821434712959760481875785781780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree087.table
  base := (72497506666790336775688715365588723651859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-228282737103371639104724930615944622000000000000)
      constant := (5379200838141536704458505305217476956719516312411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231538706786165863651/50000000000000000000)
  centralHi := (463077413572331727303/100000000000000000000)
  directionLo := (465761942807011401903/100000000000000000000)
  directionHi := (29110121425438212619/6250000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree088.table
  base := (74991873565278493447768421987241661274863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-691972666719441541426341733979167566000000000000)
      constant := (16481508566890934476497959647279404710237871816581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree088.table
  base := (74991873259327526089449494586577972624213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-692716029389610788428796904607051566000000000000)
      constant := (16515883594582133701947101891896266262122780285031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465761942807011401903/100000000000000000000)
  centralHi := (29110121425438212619/6250000000000000000)
  directionLo := (117107771884993600039/25000000000000000000)
  directionHi := (468431087539974400157/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree089.table
  base := (19381045222799825844203054839610003517643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-699832037495867307461390492526704766000000000000)
      constant := (16863387017746082529141529184055168260366082593764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree089.table
  base := (7752418063052683024271679150266313679079/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-700583847469106659543419017366269266000000000000)
      constant := (16898547536735722647057330458888252294420225953730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117107771884993600039/25000000000000000000)
  centralHi := (468431087539974400157/100000000000000000000)
  directionLo := (471085109274751497391/100000000000000000000)
  directionHi := (29442819329671968587/6250000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree090.table
  base := (20023607230724534381742185880558302291581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-235897136090764357832146417024747322000000000000)
      constant := (5749879818911525465848911766215736970559401629396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree090.table
  base := (640755429606650498341115782877116664023/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-236150555182867510219347043375162322000000000000)
      constant := (5761864780121569884476732782332551209868678895875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471085109274751497391/100000000000000000000)
  centralHi := (29442819329671968587/6250000000000000000)
  directionLo := (94744852437887296297/20000000000000000000)
  directionHi := (236862131094718240743/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree091.table
  base := (16540523518481457047369736021328201074309/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-14603077123443241623091592033097534000000000000)
      constant := (360005426192073377267332409842403216600439664835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree091.table
  base := (5168913587703247382145241225267587039463/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-14618764972002008199442106997647034000000000000)
      constant := (360755591939401618164920612406337869644028746704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94744852437887296297/20000000000000000000)
  centralHi := (236862131094718240743/50000000000000000000)
  directionLo := (238174396710397567427/50000000000000000000)
  directionHi := (95269758684159026971/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree092.table
  base := (85348746842487395087508042533819446810351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-723410149825144605566536768169316366000000000000)
      constant := (18035266297402531879614335166661276323942214620037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree092.table
  base := (42674373340692680617019738000326290829107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-724187301707594272887285355643922366000000000000)
      constant := (18072836530364494556246373128621736169436785787618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238174396710397567427/50000000000000000000)
  centralHi := (95269758684159026971/20000000000000000000)
  directionLo := (478958943334362175991/100000000000000000000)
  directionHi := (59869867916795271999/12500000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree093.table
  base := (88032816624937032357110827632527972091053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-243756506867190123867195175572284522000000000000)
      constant := (6144880232797309031676666676437102430427822760037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree093.table
  base := (44016408243871983871376769665882643428399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-244018373262363381333969156134380022000000000000)
      constant := (6157677305351789674650377525595923950471423684142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478958943334362175991/100000000000000000000)
  centralHi := (59869867916795271999/12500000000000000000)
  directionLo := (481554945781361649009/100000000000000000000)
  directionHi := (48155494578136164901/10000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree094.table
  base := (45377413449584246851852223683731390820183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-739128891377996137636634285264390766000000000000)
      constant := (18838389086114151376694683207955645727707377998842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree094.table
  base := (90754826782349603256599235546816177449463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-739922937866586015116529581162357766000000000000)
      constant := (18877610161841662052839000591440357840325448706781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481554945781361649009/100000000000000000000)
  centralHi := (48155494578136164901/10000000000000000000)
  directionLo := (484137028343228005339/100000000000000000000)
  directionHi := (24206851417161400267/5000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree095.table
  base := (11689347203875993247416274008602404887807/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-746988262154421903671683043811927966000000000000)
      constant := (19246511460345551100448085054752513917579825205672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree095.table
  base := (18702955506309754558795509700437633030633/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-747790755946081886231151693921575466000000000000)
      constant := (19286571267503125417148839012313187607215256667855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484137028343228005339/100000000000000000000)
  centralHi := (24206851417161400267/5000000000000000000)
  directionLo := (243352706282225756411/50000000000000000000)
  directionHi := (486705412564451512823/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree096.table
  base := (19262533758336911986889917494026650716591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-251615877643615889902243934119821722000000000000)
      constant := (6553002606965944357068152105005925478555570238195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree096.table
  base := (3009770897094211517321309590383213082897/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (161433146)
      previous := (80716573)
      next := (80716573)
      square := (2495333326909040505968834130419700000000000000)
      linear := (-251886191341859252448591268893597722000000000000)
      constant := (6566638410951457504418666493574979246512614704416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243352706282225756411/50000000000000000000)
  centralHi := (486705412564451512823/100000000000000000000)
  directionLo := (489260314174422240217/100000000000000000000)
  directionHi := (244630157087211120109/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree097.table
  base := (6196781272311179589330883051409812866747/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-762707003707273435741780560907002366000000000000)
      constant := (20075878167612490911896875849562685579362322375824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree097.table
  base := (99148500284907133000694257005881167696173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65445870000000000000000000000000000000000000000
      center := (484299438)
      previous := (242149719)
      next := (242149719)
      square := (7485999980727121517906502391259100000000000000)
      linear := (-763526392105073628460395919440010866000000000000)
      constant := (20117642057739377392690970540992255485649193765551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell137.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489260314174422240217/100000000000000000000)
  centralHi := (244630157087211120109/50000000000000000000)
  directionLo := (245900971649450663373/50000000000000000000)
  directionHi := (491801943298901326747/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 2326
  qDenominator := 4431
  table := BinomialMassData.Q2326_4431.Degree098.table
  base := (25505568076626326602457299336993425754799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-15725844377218351056669986111317134000000000000)
      constant := (418308622456247131026862232546571883696352875348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2326_4431.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree098.table
  base := (10202227224516366801820720635307099925281/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335630000000000000000000000000000000000000000
      center := (9883662)
      previous := (4941831)
      next := (4941831)
      square := (152775509810757581998091885535900000000000000)
      linear := (-15742738983358561215816694534678134000000000000)
      constant := (419178606980139617438343883822885123873203062030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell137.Kernel098
