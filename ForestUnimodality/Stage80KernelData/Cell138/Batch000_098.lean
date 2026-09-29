import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell138.Parameters
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch000_049
import ForestUnimodality.BinomialMassData.Q2326_4431.Batch050_099
import ForestUnimodality.BinomialMassData.Q4657_8862.Batch000_049
import ForestUnimodality.BinomialMassData.Q4657_8862.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel000
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
  base := (837871854119879352151656353/20000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (562756501656358279483960400000000000000)
      linear := (-30670031626238800775974269000000000000)
      constant := (209467963529969838037914088250000000000000) }

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
  base := (837871854119879352151656353/20000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (562756501656358279483960400000000000000)
      linear := (-30670031626238800775974269000000000000)
      constant := (209467963529969838037914088250000000000000) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel001
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
  base := (235551352501760569042338227710904894635317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-24404549185065094069328645744841018000000000000)
      constant := (4631480495965781842610315137632212822999996137237) }

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
  base := (47071034831578677979839494556534398019819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-24429484925653487304692580030165018000000000000)
      constant := (4627642553494153308488395248190054517999997546295) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel002
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
  base := (138952886572658431426383197313722183468821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-47604762228506160251933104810290618000000000000)
      constant := (2753789512645631700666165231007203026624982465781) }

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
  base := (1387471088702767174115267221048094610159/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-23827316854841473361330486690469309000000000000)
      constant := (1374901534204890272980811146373240477062498899950) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel003
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
  base := (21653844318071689184484668910428666911923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-3933609737330401468585420215318901000000000000)
      constant := (97627013632464590169316135057165516599400940534) }

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
  base := (86449312714895067040298553179328125172013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-7875531388190267348958818525745802000000000000)
      constant := (194905075865975402275832132437468946578376347877) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel004
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
  base := (5709134424022002190369727501154007359283/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-47002594157694146308571011470594909000000000000)
      constant := (610437995366593015716794004194227879422017766815) }

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
  base := (28483901441519603155174490424494092483799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-47052465638870932779298880041242909000000000000)
      constant := (609331337620920871570093912688739803738805938039) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel005
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
  base := (39524060458045171820778652082199148491801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-117205401358829358799746482006639418000000000000)
      constant := (931400365170337402654074890330511575891531293561) }

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
  base := (39433629123374590104330495849200994740703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-117330080061771324976566153433259418000000000000)
      constant := (929955674198377524057000242221038986701219673983) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel006
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
  base := (14191029098602728985364305998329643735899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-7800311911237245832352830059560501000000000000)
      constant := (43347547407451147853373184754707745369532009571) }

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
  base := (14157343934215305925744009402889672399633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-7808623824766710244140808154668501000000000000)
      constant := (43300482244023372183205090249948745140298978857) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel007
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
  base := (20821271478749699942149683905958618489023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (33657876)
      previous := (16828938)
      next := (16828938)
      square := (450980679784369085296297217431200000000000000)
      linear := (-3338894437667581452346028574235482000000000000)
      constant := (14522504969909740830372565214248056883748136847) }

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
  base := (20769300274485404520769171341888731076179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (33657876)
      previous := (16828938)
      next := (16828938)
      square := (450980679784369085296297217431200000000000000)
      linear := (-3342456686323066200255162043567482000000000000)
      constant := (14514874501379179206138775442433842766183087331) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel008
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
  base := (3839235098503186075353219304364647686727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-93403020244576278673779929601494109000000000000)
      constant := (348144807277796934546244518051822011060801580494) }

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
  base := (7657613363601053697676090221333928966829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-93502763206929851615235666742790109000000000000)
      constant := (348157123195616336330978993895772754525697513869) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel009
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
  base := (11196080205612227310842350886252598526853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-23334028170288180392240479807604202000000000000)
      constant := (79860799290417474592535909872391173011687098237) }

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
  base := (11161386944290371567340375745329050001727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-23358963910876573627604414092928202000000000000)
      constant := (79903665185453125657434595470798060121217500583) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel010
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
  base := (790102595090457586793894245407069028041/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-116603233288017344856384388666943709000000000000)
      constant := (385191235712724832464380547667969845035296461005) }

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
  base := (7871377039151577804698312996418327840923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-233455823981918622066408120187127418000000000000)
      constant := (771116821792167762933872655015030534848328201403) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel011
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
  base := (2609618558384554420246218526633768666013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-128203339809737877947686618199668509000000000000)
      constant := (423118563956621116186638997543453202517788064893) }

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
  base := (649179094986093089784193728796884789077/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-128340486382974040742188256768950509000000000000)
      constant := (423661336305206219748387414576698890473092914388) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel012
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
  base := (1498365869022905208309151500783559611413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-15533716259050934559887649748043701000000000000)
      constant := (52404884331937383136645112969871410015526190477) }

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
  base := (594805594654687121370122749319742731529/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-31100680172219726766927211876519402000000000000)
      constant := (104970693746305652890036098341491109206848639205) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel013
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
  base := (1771361472600006215600752567714647331/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-151403552853178944130291077265118109000000000000)
      constant := (529787318453587032577571676082807706606765405120) }

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
  base := (1113583452463477392004792693081780228059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-303131270334007000320313300239448218000000000000)
      constant := (1061402420370799061532097769852163225452235899899) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel014
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
  base := (-5484241373685109460395290094549520879/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (16828938)
      previous := (8414469)
      next := (8414469)
      square := (225490339892184542648148608715600000000000000)
      linear := (-3326605293365295453501904220364141000000000000)
      constant := (12181087504200492691056224058086405881140574760) }

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
  base := (-456551364856146466267366583479144661223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (33657876)
      previous := (16828938)
      next := (16828938)
      square := (450980679784369085296297217431200000000000000)
      linear := (-6660335084041560402822075379392282000000000000)
      constant := (24407619057949966420502423329379503004839217353) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel015
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
  base := (-177051706718941336429770628132599696467/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-19400418432957778923655059592285301000000000000)
      constant := (74712317480309592561449883749152779583830209785) }

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
  base := (-1786312728626813538412959944883132819843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-38842396433562879906250009660110602000000000000)
      constant := (149718727525157053777663206849007249142660720053) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel016
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
  base := (-2899610795967927566189694226201509464457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-372407744836681086808395531726585018000000000000)
      constant := (1512054975632920573953694162177136073335613267223) }

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
  base := (-2913603438883567682362485318856101880719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-372806716686095378574218480291769018000000000000)
      constant := (1515143887514275606984022774432606070282312645841) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel017
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
  base := (-1927863583332857971388191545510437882251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-197803978940061076495499995396017309000000000000)
      constant := (847431552353129146574717932194572977614537723989) }

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
  base := (-1934051016849235912116503420342298805391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-198015932735062418996093436821271309000000000000)
      constant := (849208325939899219645718693130165212564367594449) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel018
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
  base := (-2331314214091583273248465710469496373989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-23267120606864623287422469436526901000000000000)
      constant := (105154419974991838436915394900227818044748150819) }

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
  base := (-4673551595800965718441948346362420248363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-46584112694906033045572807443701802000000000000)
      constant := (210757852756807659235453589254736981718008912973) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel019
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
  base := (-2669798543501445261517975240107797310751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-221004191983502142678104454461466909000000000000)
      constant := (1052712876019972216104255027340808459364272135489) }

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
  base := (-2674609894775390871349593834944827460307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-221241081519091878414061830172044909000000000000)
      constant := (1054988829795809942469520028398778977958095375373) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel020
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
  base := (-5902427949342276540458765638217102153393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-465208597010445351538813367988383418000000000000)
      constant := (2332491570726218791028631773132317510207696498927) }

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
  base := (-2955444314290946956064142393449151558769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-232853655911106608123046026847431709000000000000)
      constant := (1168788872968531553729082142372190622642351999791) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel021
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
  base := (-6364138094049775025055516905842203343601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3739764)
      previous := (1869882)
      next := (1869882)
      square := (50108964420485453921810801936800000000000000)
      linear := (-1107502970643733373517954256357898000000000000)
      constant := (5836103041708951332051504621146667264939539879) }

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
  base := (-254862536874885380353306609767881975663/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3739764)
      previous := (1869882)
      next := (1869882)
      square := (50108964420485453921810801936800000000000000)
      linear := (-1108690386862228289487665412801898000000000000)
      constant := (5848901566257135345468371321237566164037689425) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel022
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
  base := (-3367749184650801664163037288620154576731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-255804511548663741952011143059641309000000000000)
      constant := (1414451945891685767031676952087687973257407384709) }

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
  base := (-3371001935245582812697654411732028309801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-256078804695136067541014420198205309000000000000)
      constant := (1417564970269693717371334181430206513120133208439) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel023
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
  base := (-7025444935794844739766764999578805947613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-534809236140768550086626745184732218000000000000)
      constant := (3097863471452006654211488190003117067359187837507) }

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
  base := (-3515567752173457008646259014517145560789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-267691379087150797249998616873592109000000000000)
      constant := (1552347776838012381854493475397253048157257802571) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel024
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
  base := (-1448281117822175085904992284518982344053/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-62001049909356624029914578250020202000000000000)
      constant := (375606038315150144678149726027307752829802014815) }

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
  base := (-7246376019146853480810479572183425972279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-62067545217592339324218403010884202000000000000)
      constant := (376435199207179711980051315441942590922120165409) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel025
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
  base := (-7389562693408155156501273656624772401197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-581209662227650682451835663315631418000000000000)
      constant := (3676555128876103312704559741132938851995501988083) }

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
  base := (-739389826098347776022066973450910645539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-290916527871180256667967010224365709000000000000)
      constant := (1842336230960147780504035871489643913265657789105) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel026
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
  base := (-7475067296738599178382095728386441807087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-604409875271091748634440122381081018000000000000)
      constant := (3986064689124911866253456737392214413919245735793) }

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
  base := (-7478844390512008578308906050320872181787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-605058204526389972753902413799505018000000000000)
      constant := (3994861600889730996564631667141676820271245489093) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel027
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
  base := (-7502214708975739356463750804056302291831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-69734454257170312757449397938503402000000000000)
      constant := (478766521388366566439940151533347342917604210401) }

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
  base := (-3752750746530956839479171703197293602439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-34904630739467746231770600397237701000000000000)
      constant := (239911113231343241030529474249539495784764850769) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel028
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
  base := (-3737294571373053918384073787513325459061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (16828938)
      previous := (8414469)
      next := (8414469)
      square := (225490339892184542648148608715600000000000000)
      linear := (-6640921442428304908159684086856941000000000000)
      constant := (47397824157277372381722064942306681135134306971) }

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
  base := (-7477446231870935489515540373626827518561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (33657876)
      previous := (16828938)
      next := (16828938)
      square := (450980679784369085296297217431200000000000000)
      linear := (-13296091879478548807955902051041882000000000000)
      constant := (95004439803927556448258901140324596108415311471) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel029
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
  base := (-3697591620028480238437729122645311302411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-337005257200707473591126749788714909000000000000)
      constant := (2497135078530316515413890299818977976117863702229) }

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
  base := (-147953287379454630836237411722915292217/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-337366825439239175503903796925912909000000000000)
      constant := (2502627757918187536437135721530042856734156546575) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel030
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
  base := (-7266497060784572968615751027876255937213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-77467858604984001484984217626986602000000000000)
      constant := (595188863984394913745890539751948899261547661323) }

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
  base := (-7268649733550775676088130421488065202173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-77550977740278645602863998578066602000000000000)
      constant := (596496107916643289861027379946447972607568737483) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel031
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
  base := (-7090620192965275182046444502081898946657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-720410940488297079547462417708329018000000000000)
      constant := (5732234597337852312078596726071903861655184713023) }

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
  base := (-1773121575404607643365043426981271462139/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-360591974223268634921872190276686509000000000000)
      constant := (2872402500172858888951131598937264235772484650442) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel032
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
  base := (-6869299946445565397350492568344615757737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-743611153531738145730066876773778618000000000000)
      constant := (6120840315231608202004503051395848144575757841143) }

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
  base := (-3435458176051697831969666580329517757773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-372204548615283364630856386952073309000000000000)
      constant := (3067120697818048896722321522153907315098629025747) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel033
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
  base := (-132079960898984818277705782875756474961/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-42600631476398845106259518657734901000000000000)
      constant := (362360457244810045961261405999317664323370115775) }

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
  base := (-6605397117293171203361780888878467415353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-85292694001621798742186796361657802000000000000)
      constant := (726305060685608376896206633385690696857852385263) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel034
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
  base := (-6295937796168819265889129122905241671577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-790011579618620278095275794904677818000000000000)
      constant := (6937154324731905837217659496841503411373016688903) }

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
  base := (-6297147909503860847105249354546220478729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-790859394798625648097649560605693818000000000000)
      constant := (6952293512262251838145000402484613425667329230231) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel035
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
  base := (-2973071684140158461976431458410038889727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (16828938)
      previous := (8414469)
      next := (8414469)
      square := (225490339892184542648148608715600000000000000)
      linear := (-8298079516959809635488574020103341000000000000)
      constant := (75151209080963178759527768695902649927314178097) }

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
  base := (-1486797338512526440931323064835941150213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (16828938)
      previous := (8414469)
      next := (8414469)
      square := (225490339892184542648148608715600000000000000)
      linear := (-8306985138598521505261407693433341000000000000)
      constant := (75314951583652335889570251977005375652924606486) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel036
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
  base := (-1111094503143494450032477316661357883277/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-92934667300611378940053857003953002000000000000)
      constant := (867273765007609906845907207709933434991263047335) }

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
  base := (-1389094018137695689270872629831371759023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-46517205131482475940754797072624501000000000000)
      constant := (434580221974494231606058356526054640795820627666) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel037
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
  base := (-5124643863592336227119322159804611000599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-859612218748943476643089172101026618000000000000)
      constant := (8259076400820500159543774703118912096916268377161) }

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
  base := (-5125423926773075700436827425685854182241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-860534841150714026351554740658014618000000000000)
      constant := (8277015678232307667527915672131678028905029761599) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel038
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
  base := (-2327129834297063920805246008865998406949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-441406215896192271412846815583238109000000000000)
      constant := (4362822106313263867681158102498555038251582594811) }

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
  base := (-4654932741366563611765682964973166106679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-883759989934743485769523134008788218000000000000)
      constant := (8744568526458351669844838974389537759248164010281) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel039
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
  base := (-2072412408302744576561597312213483085593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-50334035824212533833794338346218101000000000000)
      constant := (511397633759878878934681554132256326457769388303) }

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
  base := (-4145405266023121042762576570147962726877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-100776126524308105020832391928840202000000000000)
      constant := (1025010296594637231918878583578662218020398745067) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel040
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
  base := (-3596762687370423873147042466055221024631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-929212857879266675190902549297375418000000000000)
      constant := (9697607673437670405875130005733430297600219832809) }

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
  base := (-3597263007529283808071306151052580125553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-930210287502802404605459920710335418000000000000)
      constant := (9718579831148951197600463877292800663381542405167) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel041
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
  base := (-150521420465185047335310824587865176069/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-476206535461353870686753504181412509000000000000)
      constant := (5101494018699829804089037695539690390328383344910) }

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
  base := (-3010859454815204245845109845501678980987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-953435436286831864023428314061109018000000000000)
      constant := (10225023071532829244135616990670121752788577697893) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel042
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
  base := (-477223987776771953895263658328975607949/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3739764)
      previous := (1869882)
      next := (1869882)
      square := (50108964420485453921810801936800000000000000)
      linear := (-2212275020331403191737214211855498000000000000)
      constant := (24311321200810656198660600760242614384792512855) }

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
  base := (-1193245565687190405798040516172656629827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1869882)
      previous := (934941)
      next := (934941)
      square := (25054482210242726960905400968400000000000000)
      linear := (-1107324926384196511838318262371749000000000000)
      constant := (12181878195727853733725592991303740154183472133) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel043
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
  base := (-172408732571766946933261498217878811027/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-499406748504794936869357963246862109000000000000)
      constant := (5626258300248486141564998602960257709486658587265) }

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
  base := (-215550854502367955890645300642238315443/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-499942866927445391429682550381328109000000000000)
      constant := (5638377718794974998763258070926094030138198115508) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel044
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
  base := (-256135115901629191188733725238257448677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-511006855026515469960660192779586909000000000000)
      constant := (5898327884606673249220442485069300186392412031606) }

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
  base := (-1024815372143157566674829345445955349247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1023110882638920242277333494113429818000000000000)
      constant := (11822035578810839273143700203546929086256212872033) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel045
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
  base := (-143827788788725467797812462990862788433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-58067440172026222561329158034701301000000000000)
      constant := (686317038652586595858119174112734576092012545943) }

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
  base := (-143946007640186328284906635479649418543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-58129779523497205649738993748011301000000000000)
      constant := (687791863943150215381849781020556023383615307753) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel046
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
  base := (486419344947206377609518528943020239853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1068414136139913072286529303690073018000000000000)
      constant := (12923666474546928094990369958859330130007436477133) }

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
  base := (486216073058910080951361601291513666737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1069561180206979161113270280814977018000000000000)
      constant := (12951406464753618233047092056851536128660947907857) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel047
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
  base := (162195000670695173448301200383634403493/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-545807174591677069234566881377761309000000000000)
      constant := (6753266332582706195153417600672718502758236508692) }

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
  base := (1297385311978921873652262870212906044981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1092786328991008620531238674165750618000000000000)
      constant := (13535491893783810651679734649735784797402612203541) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel048
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
  base := (33525968482064069730338833277485143361/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-61934142345933066925096567878942901000000000000)
      constant := (783461289857137780780588595767462972393957727008) }

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
  base := (2145511903758135116544041843389225653527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-124001275308337564438800785279613802000000000000)
      constant := (1570278644458624923913330041570078110050713102783) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel049
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
  base := (75765938509546262395391853629643461363/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (16828938)
      previous := (8414469)
      next := (8414469)
      square := (225490339892184542648148608715600000000000000)
      linear := (-11612395666022819090146353886596141000000000000)
      constant := (150112004170697468502064130304523878177801582140) }

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
  base := (47351697685609837689232454974553847653/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (16828938)
      previous := (8414469)
      next := (8414469)
      square := (225490339892184542648148608715600000000000000)
      linear := (-11624863536317015707828321029258141000000000000)
      constant := (150433188487647695916296946927570629713191453344) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel050
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
  base := (3952412947097553836188564585541944521137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1161214988313677337016947139951871418000000000000)
      constant := (15332550791450998245934214459287005994203263306257) }

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
  base := (158092091758690855102568077873272512489/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1162461775343096998785143854218071418000000000000)
      constant := (15365324470353412339458877090980226669951963528225) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel051
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
  base := (1227731558225533950088802033083742694851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-65800844519839911288863977723184501000000000000)
      constant := (887056952716130218950627392436874534234711214358) }

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
  base := (1227707816418830208819050456094141319693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-65871495784840358789061791531602501000000000000)
      constant := (888951254837764056733339655190778740538017101194) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel052
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
  base := (1181225060998871586158683287871842559389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1207615414400559469382156058082770618000000000000)
      constant := (16614398458268779662354521285387160833203359660145) }

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
  base := (5906043825368922595184616792613191234233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1208912072911155917621080640919618618000000000000)
      constant := (16649845806085615525279366719120345158140225740313) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel053
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
  base := (6937966367598699433853026708552146773929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1230815627444000535564760517148220218000000000000)
      constant := (17274669859710516024750841509869012789796243016969) }

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
  base := (867237060124479514754475716040893566671/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-616068610847592688519524517135196109000000000000)
      constant := (8655746636729220380717209379923122141557823918524) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel054
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
  base := (4003206297879875937654910191147187771539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-69667546693746755652631387567426101000000000000)
      constant := (997102146122398872413628400540957417392057703131) }

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
  base := (8006352670123456244308077179861606608977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-139484707831023870717446380846796202000000000000)
      constant := (1998451585704462820150650461259349048804074985833) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel055
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
  base := (9111433022098660909772738763096759439031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1277216053530882667929969435279119418000000000000)
      constant := (18633904161740655475766710886988349934700428725591) }

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
  base := (4555690826073896170256557719040917308399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-639293759631622147937492910485969709000000000000)
      constant := (9336779098088558818649762353329169902153869258639) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel056
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
  base := (10253001602131312804514812930362914662083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (33657876)
      previous := (16828938)
      next := (16828938)
      square := (450980679784369085296297217431200000000000000)
      linear := (-26539107481108647634950487639685082000000000000)
      constant := (394548284550444222130405333787366217913035375187) }

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
  base := (10252957578367681780930119240556207281327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (33657876)
      previous := (16828938)
      next := (16828938)
      square := (450980679784369085296297217431200000000000000)
      linear := (-26567605470352525618223555394341082000000000000)
      constant := (395387235519634219221426444104158338139347634303) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel057
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
  base := (5715548214673258118229939286759309109479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-73534248867653600016398797411667701000000000000)
      constant := (1113595752432739380836233967813581870842292613391) }

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
  base := (44652573090651035410937862705411459861/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-73613212046183511928384589315193701000000000000)
      constant := (1115961826522481209441707743234182804747245756032) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel058
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
  base := (2529139815184255839348959799522463413491/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1346816692661205866477782812475468218000000000000)
      constant := (20769476602385809012346832374599928227958632348255) }

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
  base := (6322833384267295789463796271452928317821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-674131482807666337064445500512130109000000000000)
      constant := (10406786424028949386772506128142181284342229554781) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel059
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
  base := (6948397019431124822446707984823025794277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-685008452852323466330193635770458909000000000000)
      constant := (10753562407189600548861076500251222041741669785797) }

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
  base := (13896766372944584238109808273723702926027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1371488114399362133546859394375033818000000000000)
      constant := (21552754150505456328209026299700525020284614797547) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel060
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
  base := (15184368274634555767987527297564460527581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-154801902083120888760332414511818602000000000000)
      constant := (2473074213741759871426411178218170020010273251349) }

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
  base := (1898043073638191079499871320456373681577/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-77484070176855088498045988206989301000000000000)
      constant := (1239158696154340826545391056399061899684787964932) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel061
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
  base := (16508410808077388804839202018521174281439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1416417331791529065025596189671817018000000000000)
      constant := (23021105714792037991909605272374161017281120062079) }

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
  base := (8254195267520737817013854066627039949931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-708969205983710526191398090538290509000000000000)
      constant := (11534939887610909714617131376316732930014397220491) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel062
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
  base := (8934456201848880444158589870593249299697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-719808772417485065604100324368633309000000000000)
      constant := (11898719003200168251989356041791101452963668270417) }

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
  base := (17868895055475254713115708128438943928763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1441163560751450511800764574427354618000000000000)
      constant := (23847823704083986127732828709669069954189733767643) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel063
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
  base := (19265865289353292800574675243413826484763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3739764)
      previous := (1869882)
      next := (1869882)
      square := (50108964420485453921810801936800000000000000)
      linear := (-3317047070019073009956474167353098000000000000)
      constant := (55752074026993987409320749029291830968928133523) }

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
  base := (9632925223643745223303599255519128775397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1869882)
      previous := (934941)
      next := (934941)
      square := (25054482210242726960905400968400000000000000)
      linear := (-1660304659337278878932803818342549000000000000)
      constant := (27935020596511825625528916585966061632209449837) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel064
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
  base := (206992629239427878868013431796134636127/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-743008985460926131786704783434082909000000000000)
      constant := (12694392752438828125285137083268937104476974182350) }

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
  base := (2069925022874519066050721686898294623521/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-743806929159754715318350680564450909000000000000)
      constant := (12721236517039677608513101201444953675728981462405) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel065
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
  base := (22169099802070729161692473492433771268481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1509218183965293329756014025933615418000000000000)
      constant := (26203800475228640122197270428002394793414022787041) }

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
  base := (22169088945497080893040454709428065793777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1510839007103538890054669754479675418000000000000)
      constant := (26259178200862331840834022589222805085487292905297) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel066
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
  base := (23675371289781258047306177726391034175587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-170268710778748266215402053888785002000000000000)
      constant := (3003523273997257583391369799609736978394034132523) }

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
  base := (23675362007458406113222888565875031804511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-170451572876396483274737571981161002000000000000)
      constant := (3009867064039081447013119675140126094257463077319) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel067
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
  base := (25218073486404191680478619357969661730783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1555618610052175462121222944064514618000000000000)
      constant := (27872512400532864525383793001847812259673039764863) }

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
  base := (25218065551651495203865893764131441132669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1557289304671597808890606541181222618000000000000)
      constant := (27931349084702778420826881415233100128784392438109) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel068
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
  base := (26797203108349896995913630891436308935481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1578818823095616528303827403129964218000000000000)
      constant := (28726209214432064869099942497255736140361398374041) }

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
  base := (5359439265371925265598914667586413654669/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1580514453455627268308574934531996218000000000000)
      constant := (28786814662081855958209789516103424426714538400545) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel069
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
  base := (28412757391356173520608438007219028022357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-178002115126561954942936873577268202000000000000)
      constant := (3288088872600006210694417028820443466982584443853) }

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
  base := (7103187899153852254606751430325304931973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-89096644568869818207030184882376101000000000000)
      constant := (1647511125264545494807804065962499735785884253434) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel070
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
  base := (15032367004124723404163409180605142998797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (16828938)
      previous := (8414469)
      next := (8414469)
      square := (225490339892184542648148608715600000000000000)
      linear := (-16583869889617333272133023686335341000000000000)
      constant := (310941676242302733067756285195770514143044971133) }

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
  base := (15032364528800858064945329746582353600687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (16828938)
      previous := (8414469)
      next := (8414469)
      square := (225490339892184542648148608715600000000000000)
      linear := (-16601681132894757011678691032995341000000000000)
      constant := (311596998137958053920837135378688281681905673343) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel071
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
  base := (15876565499875946130733950752403035127271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-824209731112969863425820390163156509000000000000)
      constant := (15682331215500454080760906951440219861363443396231) }

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
  base := (6350625354202094251833132600413101837047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1650189899807715646562480114584317018000000000000)
      constant := (31430731312289972694343929165007411046686208718835) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel072
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
  base := (33477946716260114615540427258151667340287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-185735519474375643670471693265751402000000000000)
      constant := (3585548255419762005720365992389854972701188958823) }

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
  base := (16738971552398406034826301857256610417441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-92967502699541394776691583774171701000000000000)
      constant := (1796548705946049464913969359032773248067349647289) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel073
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
  base := (35239179768851856554991835262690606447951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1694819888312821859216849698457212218000000000000)
      constant := (33188099847806749862810495482052303427944128873711) }

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
  base := (17619588342547716289630512987865352627833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-848320098687887282699208450642932109000000000000)
      constant := (16628970987381249621360181436575990523175595069913) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel074
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
  base := (37036828988055079693733586634254602555911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1718020101356262925399454157522661818000000000000)
      constant := (34119159055126449097648130457220298951732745711271) }

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
  base := (37036826355342410239671095948836911296849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1719865346159804024816385294636637818000000000000)
      constant := (34190927092783099680614449827580563246380533319089) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel075
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
  base := (7774178677829435905236066439684131265809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-193468923822189332398006512954234602000000000000)
      constant := (3895901322378127498648445882913390315980845209805) }

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
  base := (1943544557093902490764242144967738298219/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-96838360830212971346352982665967301000000000000)
      constant := (1952046224554116107252507782021663764119753968510) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel076
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
  base := (40741372142948208505273706220083702626009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1764420527443145057764663075653561018000000000000)
      constant := (36019958370356924117242662743159302945354133089849) }

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
  base := (40741370225001350023832756325125624705219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1766315643727862943652322081338185018000000000000)
      constant := (36095656806241656441875660512793761758437965298659) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel077
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
  base := (42648264551236777900220730691741245164133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (33657876)
      previous := (16828938)
      next := (16828938)
      square := (450980679784369085296297217431200000000000000)
      linear := (-36482055928297675998923827239163482000000000000)
      constant := (754891805066919737029379534231818551783571287637) }

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
  base := (21324131457305295767523942616273013554541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (16828938)
      previous := (8414469)
      next := (8414469)
      square := (225490339892184542648148608715600000000000000)
      linear := (-18260620331754004112962147700907741000000000000)
      constant := (378238789510576601954963977089641657028155478749) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel078
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
  base := (44591570026055811916411613672769305887319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-201202328170003021125541332642717802000000000000)
      constant := (4219148013736196419446284722844221527103057130751) }

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
  base := (11147892157425565475570289261153939255221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-100709218960884547916014381557762901000000000000)
      constant := (2114003651552853193118863036695268516899006025818) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel079
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
  base := (23285644036145874568294894817414251807079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-917010583286734128156238226424954909000000000000)
      constant := (19483929693338042383124161022305851463974007194119) }

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
  base := (1164282172027906798602038957225817093503/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-917995545039975660953113630695252909000000000000)
      constant := (19524824932191077806903780199130327175371051095660) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel080
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
  base := (1943496730920346426353685628040965409441/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1857221379616909322495080911915359418000000000000)
      constant := (39976280229243997707761721195240458566455793440025) }

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
  base := (48587417257012699935454360647100558519001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1859216238863980781324195654741279418000000000000)
      constant := (40060153773242934811183292745953131548928579592761) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel081
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
  base := (12659990069275261733313238352084104034649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-104467866258908354926538076165600501000000000000)
      constant := (2277644146913110285311561514955935992781207596642) }

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
  base := (50639959410647078782458602150975625563529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-209160154183112248971351560899117002000000000000)
      constant := (4564841938636199674807992256467281212459979855841) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel082
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
  base := (10545782757779655078681035286116832137617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1903621805703791454860289830046258618000000000000)
      constant := (42031802626446920515259631254447896397335456437685) }

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
  base := (26364456525039998094092744571652182679639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-952833268216019850080066220721413309000000000000)
      constant := (21059960441049436876277752395775528772860371692279) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel083
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
  base := (6856784819926477285678884004983964307871/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-963411009373616260521447144555854109000000000000)
      constant := (21539452085194111300527493581401708918213078531324) }

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
  base := (13713569482378647386252943067684258120727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-964445842608034579789050417396800109000000000000)
      constant := (21584592035768123997023052270071318999309326128494) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel084
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
  base := (57016054378965399403780800330426750665833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3739764)
      previous := (1869882)
      next := (1869882)
      square := (50108964420485453921810801936800000000000000)
      linear := (-4421819119706742828175734122850698000000000000)
      constant := (100088206966311014736064450258447201366393550993) }

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
  base := (57016053842004132920747509606449223678593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3739764)
      previous := (1869882)
      next := (1869882)
      square := (50108964420485453921810801936800000000000000)
      linear := (-4426568784580722492054578748626698000000000000)
      constant := (100297884380895186487661247228084177887394638953) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel085
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
  base := (59214241070989333560600974896353354030933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1973222444834114653408103207242607418000000000000)
      constant := (45211787928244998209084383966229280904591725129013) }

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
  base := (59214240613312800053422136445507174197823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1975341982784128078414037621495147418000000000000)
      constant := (45306469699993556923127967797426805836985423502303) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel086
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
  base := (30724419243397490800068425982920816838889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-998211328938777859795353833154028509000000000000)
      constant := (23148785067887213763947770477866829603739522131529) }

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
  base := (61448838096747076841719711440466993636491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-1998567131568157537832006014845921018000000000000)
      constant := (46394492132712441644138810871761956859447385172651) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel087
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
  base := (63719846501174386815823611757880932275789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-224402541213444087308145791708167402000000000000)
      constant := (5266249543585904706418094747766657236306669701381) }

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
  base := (15929961542201056105429384341256095101109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-112321793352899277624998578233149701000000000000)
      constant := (2638635239317033785910637193931886330279654431322) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel088
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
  base := (16506816252173669959039151223209015996287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-1021411541982218925977958292219478109000000000000)
      constant := (24253907597835549469950988396209746578232551690814) }

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
  base := (3301363236275426456620377405209020611491/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-1022508714568108228333971400773734109000000000000)
      constant := (24304648111467311059030638132644354869300881476510) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel089
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
  base := (17092773480144368264532275173242374451781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-1033011648503939459069260521752202909000000000000)
      constant := (24816139022112621815075058055887163296117548356682) }

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
  base := (6837109367932654919493301921553182542269/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-1034121288960122958042955597449120909000000000000)
      constant := (24868038938338936441877371707180610147621409718545) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel090
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
  base := (70751333162070830048562645349310826529343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-232135945561257776035680611396650602000000000000)
      constant := (5641070492940879419365672495058838978087731105447) }

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
  base := (17687833239142448465110818759849059560709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-116192651483570854194659977124945301000000000000)
      constant := (2826432181527198790425456985966709133108827888122) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel091
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
  base := (18291995667559002288520581585141864079087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (16828938)
      previous := (8414469)
      next := (8414469)
      square := (225490339892184542648148608715600000000000000)
      linear := (-21555344113211847454119693486074541000000000000)
      constant := (529794738481259062867976305590267342751970581886) }

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
  base := (18291995623801941322385672126112238416569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (16828938)
      previous := (8414469)
      next := (8414469)
      square := (225490339892184542648148608715600000000000000)
      linear := (-21578498729472498315529061036732541000000000000)
      constant := (530902044838284144698796052429018601897793232082) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel092
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
  base := (18905260598020870090969587959673932406281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-1067811968069101058343167210350377309000000000000)
      constant := (26541513923635640011363712859756355341590152105682) }

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
  base := (37810521121513245214474137563763761581397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-1068959012136167147169908187475281309000000000000)
      constant := (26596970627819760037218753601790638013350130744117) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel093
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
  base := (78110512283003067315785954505672764695837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (183248436)
      previous := (91624218)
      next := (91624218)
      square := (2455339256603787242168729294903200000000000000)
      linear := (-239869349909071464763215431085133802000000000000)
      constant := (6028784984879524979825078142888192956694144594773) }

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
  base := (39055256078038967231382855835642355512907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-120063509614242430764321376016740901000000000000)
      constant := (3020688991727207483196097766684127867679716494803) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel094
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
  base := (40318196152720890462647378143198339395607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-1091012181112542124525771669415826909000000000000)
      constant := (27723997710179708067817812541267881087290232287927) }

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
  base := (16127278439474865157883411994699420501907/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-2184368321840393213175753161652109818000000000000)
      constant := (55563782179776280982210802467493026006864710411135) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel095
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
  base := (83198682427790247095430863338204128685951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1649235924)
      previous := (824617962)
      next := (824617962)
      square := (22098053309434085179518563654128800000000000000)
      linear := (-2205224575268525315234147797897103418000000000000)
      constant := (56649819515981743077977614854192563691833205991711) }

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
  base := (8319868233578869287025863196212314841149/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-1103796735312211336296860777501441709000000000000)
      constant := (28384041120544009704318551384676217316739362156945) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel096
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
  base := (42898691311722403371761971262693333337997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-123801377128442576745375125386808501000000000000)
      constant := (3214696508347798653405391335465958940783507257413) }

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
  base := (42898691272564516331044557467889770568743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (91624218)
      previous := (45812109)
      next := (45812109)
      square := (1227669628301893621084364647451600000000000000)
      linear := (-123934367744914007333982774908536501000000000000)
      constant := (3221405668583927913830398525412627959299059348047) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel097
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
  base := (4421624643500878284987497181785770269651/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-1125812500677703723799678358014001309000000000000)
      constant := (29546074161377877811085146910600476324752332874110) }

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
  base := (44216246401679340580105309635027236167399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (824617962)
      previous := (412308981)
      next := (412308981)
      square := (11049026654717042589759281827064400000000000000)
      linear := (-1127021884096240795714829170852215309000000000000)
      constant := (29607720779805833754417736644813775348901267957639) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell138.Kernel098
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
  base := (22776003287167762370238951293200293460217/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (16828938)
      previous := (8414469)
      next := (8414469)
      square := (225490339892184542648148608715600000000000000)
      linear := (-23212502187743352181448583419320941000000000000)
      constant := (615639316664265634579097331293828892772561779026) }

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
  base := (91104013091939792337427469297601762961367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (33657876)
      previous := (16828938)
      next := (16828938)
      square := (450980679784369085296297217431200000000000000)
      linear := (-46474875856663490833625035409289882000000000000)
      constant := (1233846955429121366325494752442183398799227181863) }

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
end ForestUnimodality.Stage80KernelData.Cell138.Kernel098
