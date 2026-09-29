import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell029.Parameters
import ForestUnimodality.BinomialMassData.Q1613_3478.Batch000_049
import ForestUnimodality.BinomialMassData.Q1613_3478.Batch050_099
import ForestUnimodality.BinomialMassData.Q22_47.Batch000_049
import ForestUnimodality.BinomialMassData.Q22_47.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree000.table
  base := (4218468245178179103604065851/100000000000000000000000000)
  polynomial :=
    { denominator := 8695000000000000000000000000000000000000000
      center := (42895)
      previous := (37099)
      next := (0)
      square := (1503267448994614466084573897000000000000000)
      linear := (6141005582762735962032429867400000000000000)
      constant := (366795813918242673058373525744450000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree000.table
  base := (4218468245178179103604065851/100000000000000000000000000)
  polynomial :=
    { denominator := 117500000000000000000000000000000000000000
      center := (575)
      previous := (506)
      next := (0)
      square := (20314424986413709001142890500000000000000)
      linear := (82986561929226161649086890100000000000000)
      constant := (4956700188084360446734777374925000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree001.table
  base := (128178264347578652492400016832509890642603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (8254438313196084704179977843547600000000000000)
      constant := (383236130605443166337336827009885292999999226963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree001.table
  base := (254826427528456500668990578140939850290381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (12026134845085705605827186610800000000000000)
      constant := (556445542381305463936216979848536129291451629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24934291273026982011/50000000000000000000)
  directionHi := (49868582546053964023/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree002.table
  base := (161815672512510068106041628235188044569397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (11659335835935543140771120295373200000000000000)
      constant := (474037454571231159351368099223166704531249425037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree002.table
  base := (80040285969905306280768009564311535510029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (4225398023738446410813018941400000000000000)
      constant := (171179737099182831716169764926764181941654061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24934291273026982011/50000000000000000000)
  centralHi := (49868582546053964023/100000000000000000000)
  directionLo := (70524825772951726743/100000000000000000000)
  directionHi := (8815603221618965843/12500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree003.table
  base := (21298379373912845743035225348132116358287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (6809795045478916873182284903651200000000000000)
      constant := (302448927353887958847533722545886119267696203635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree003.table
  base := (52491340734098759108649142966479984766711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (2437728624934040018712444577400000000000000)
      constant := (108764661900192608359240463107754286349664599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70524825772951726743/100000000000000000000)
  centralHi := (8815603221618965843/12500000000000000000)
  directionLo := (86374918671207987321/100000000000000000000)
  directionHi := (43187459335603993661/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree004.table
  base := (36509978727891559518283957015259447137449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (980127127511145302796724755964600000000000000)
      constant := (99596039784616136436423785931059014536749407329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree004.table
  base := (3590819719746955780857384521619569930419/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (325029613064816813305935106700000000000000)
      constant := (35704912037701049108595921968488149881477855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86374918671207987321/100000000000000000000)
  centralHi := (43187459335603993661/50000000000000000000)
  directionLo := (24934291273026982011/25000000000000000000)
  directionHi := (19947433018421585609/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree005.table
  base := (51876899821587118344114747486605736540037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-2889286535434335661995385879792800000000000000)
      constant := (135468344684246929217468607123198126591193232477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree005.table
  base := (50940258921506296031910010745646172967121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-2275220345349545530977408301200000000000000)
      constant := (96932480226671801397301958693132396084370289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24934291273026982011/25000000000000000000)
  centralHi := (19947433018421585609/20000000000000000000)
  directionLo := (22301908102907240079/20000000000000000000)
  directionHi := (27877385128634050099/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree006.table
  base := (37826787719082605366698090901363682337747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-7738827325890961929584221271514800000000000000)
      constant := (95443617937015622029360569494591640394909795387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree006.table
  base := (37092615619588444900533782826520604435669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-5850559142958358315178557029200000000000000)
      constant := (68244814350849884041873054594984015198392821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22301908102907240079/20000000000000000000)
  centralHi := (27877385128634050099/25000000000000000000)
  directionLo := (122152581433695409089/100000000000000000000)
  directionHi := (12215258143369540909/10000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree007.table
  base := (6992182586795500788310833004474280224389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-6294184058173794098586528331618400000000000000)
      constant := (35172627268631293505831375741681579572918974138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree007.table
  base := (855599586124210792768735656084919584627/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-2356474485141792774844926439300000000000000)
      constant := (12590797752668937484171093972932698899528344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122152581433695409089/100000000000000000000)
  centralHi := (12215258143369540909/10000000000000000000)
  directionLo := (131939867652155034383/100000000000000000000)
  directionHi := (8246241728259689649/6250000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree008.table
  base := (827201717343020293580912409297819829221/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-17437908906804214464761892054958800000000000000)
      constant := (55266059388665526280622635876807704994090993525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree008.table
  base := (20191773800577263581100159597957826366951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-13001236738175983883580854485200000000000000)
      constant := (39735099653185153196025182017488838444594759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131939867652155034383/100000000000000000000)
  centralHi := (8246241728259689649/6250000000000000000)
  directionLo := (70524825772951726743/50000000000000000000)
  directionHi := (141049651545903453487/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree009.table
  base := (3759983376192707082520329483040656675541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-11143724848630420366175363723340400000000000000)
      constant := (23710723073777481766271312386778637412587448922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree009.table
  base := (7311581083842399011649821030498980392499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-8288287767892398333891001606600000000000000)
      constant := (17178251629271024836921828268772247687030291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70524825772951726743/50000000000000000000)
  centralHi := (141049651545903453487/100000000000000000000)
  directionLo := (149605747638161892067/100000000000000000000)
  directionHi := (37401436909540473017/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree010.table
  base := (10514951013039694350054755900807373151137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-27136990487717466999939562838402800000000000000)
      constant := (45198194298023829799348923587693494101189575577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree010.table
  base := (10150223522246909111347200857548605271947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-20151914333393609451983151941200000000000000)
      constant := (33071811334620018329413409806324869045730923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149605747638161892067/100000000000000000000)
  centralHi := (37401436909540473017/25000000000000000000)
  directionLo := (157698304529649210199/100000000000000000000)
  directionHi := (788491522648246051/500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree011.table
  base := (424189012637399322227089387543638893509/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-15993265639087046633764199115062400000000000000)
      constant := (23817208937375284465047758439350504354218644712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree011.table
  base := (6461982559462575439185796861693897907763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-23727253131002422236184300669200000000000000)
      constant := (35194079433113602876754442394681820478248467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157698304529649210199/100000000000000000000)
  centralHi := (788491522648246051/500000000000000000)
  directionLo := (82697688566063590233/50000000000000000000)
  directionHi := (165395377132127180467/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree012.table
  base := (3659214494486440366571070532044022466603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-36836072068630719535117233621846800000000000000)
      constant := (54134550789019603429759673461305101265725930963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree012.table
  base := (841520575751490261378334729175328246537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-6825647982152808755096362349300000000000000)
      constant := (10074597748329757919337608734348300096600233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82697688566063590233/50000000000000000000)
  centralHi := (165395377132127180467/100000000000000000000)
  directionLo := (86374918671207987321/50000000000000000000)
  directionHi := (172749837342415974643/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree013.table
  base := (501930341267067011112264957503630379827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-20842806429543672901353034506784400000000000000)
      constant := (32156265051369413272983639523846286207872807067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree013.table
  base := (147537461321575488618173930527510760901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-30877930726220047804586598125200000000000000)
      constant := (48108984514427667362890530604276356354151545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86374918671207987321/50000000000000000000)
  centralHi := (172749837342415974643/100000000000000000000)
  directionLo := (44950932851126526141/25000000000000000000)
  directionHi := (35960746280901220913/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree014.table
  base := (-50644874482943030911556542489496676867/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-46535153649543972070294904405290800000000000000)
      constant := (77905001362341101270527641267152220501407277325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree014.table
  base := (-1508608687988231678956142282180474666457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-34453269523828860588787746853200000000000000)
      constant := (58437197571950777042652889639463331461796487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44950932851126526141/25000000000000000000)
  centralHi := (35960746280901220913/20000000000000000000)
  directionLo := (186591150251388859511/100000000000000000000)
  directionHi := (23323893781423607439/12500000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree015.table
  base := (-3213269674849421494897349613657313462817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-51384694440000598337883739797012800000000000000)
      constant := (94722846517515127554092569025791531553512391143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree015.table
  base := (-1717189085149943142534236225695603957663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-19014304160718836686494447790600000000000000)
      constant := (35573508268272079557593919411438410857522433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186591150251388859511/100000000000000000000)
  centralHi := (23323893781423607439/12500000000000000000)
  directionLo := (38628037939967373347/20000000000000000000)
  directionHi := (12071261856239804171/6250000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree016.table
  base := (-4884643130383734735472816195485896547661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-56234235230457224605472575188734800000000000000)
      constant := (114623749301194417234230463527367795046390869019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree016.table
  base := (-5086144087809006198389472716334835748583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-41603947119046486157190044309200000000000000)
      constant := (86135672217220252691171713892816347831380153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38628037939967373347/20000000000000000000)
  centralHi := (12071261856239804171/6250000000000000000)
  directionLo := (199474330184215856089/100000000000000000000)
  directionHi := (19947433018421585609/10000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree017.table
  base := (-6317061797128163221700421201553824988783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-61083776020913850873061410580456800000000000000)
      constant := (137496362883213404934558569102881945221096565257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree017.table
  base := (-6500432991114198758251674331643629356737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-45179285916655298941391193037200000000000000)
      constant := (103322477463706734158018953307799222750967967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199474330184215856089/100000000000000000000)
  centralHi := (19947433018421585609/10000000000000000000)
  directionLo := (25701679154651722091/12500000000000000000)
  directionHi := (205613433237213776729/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree018.table
  base := (-3770104476515148420892758879323968366513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-32966658405685238570325122986089400000000000000)
      constant := (81625460719690973587383712524601121459492339927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree018.table
  base := (-3853384266674728809007969307631420231223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-24377312357132055862796170882600000000000000)
      constant := (61321107263115305767727707208242192709228393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25701679154651722091/12500000000000000000)
  centralHi := (205613433237213776729/100000000000000000000)
  directionLo := (211574477318855180229/100000000000000000000)
  directionHi := (21157447731885518023/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree019.table
  base := (-8578540032613589143023696421681001995373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-70782857601827103408239081363900800000000000000)
      constant := (191813468776593543089955942761815326564750607867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree019.table
  base := (-69836117597570678039746502469922389309/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-52329963511872924509793490493200000000000000)
      constant := (144041063361525836505656218862292680252052375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211574477318855180229/100000000000000000000)
  centralHi := (21157447731885518023/10000000000000000000)
  directionLo := (54343027943966374067/25000000000000000000)
  directionHi := (217372111775865496269/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree020.table
  base := (-2363127282193626548774224296169620353213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-37816199196141864837913958377811400000000000000)
      constant := (111561074621492019406505752092024463055642298454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree020.table
  base := (-4794532752371393109471760332096106118301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-27952651154740868646997319610600000000000000)
      constant := (83736986795683807077268230938399701584673091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54343027943966374067/25000000000000000000)
  centralHi := (217372111775865496269/100000000000000000000)
  directionLo := (22301908102907240079/10000000000000000000)
  directionHi := (223019081029072400791/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree021.table
  base := (-10179397876949713701365894336904061654323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-80481939182740355943416752147344800000000000000)
      constant := (257124701081915069420421021211480652165867074917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree021.table
  base := (-321957942347552814676687033757465010347/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-14870160276772637519548946987300000000000000)
      constant := (48225719265575979212047850319238078337147816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22301908102907240079/10000000000000000000)
  centralHi := (223019081029072400791/100000000000000000000)
  directionLo := (22852655431744591741/10000000000000000000)
  directionHi := (228526554317445917411/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree022.table
  base := (-134673815997256131585466820996074317877/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-42665739986598491105502793769533400000000000000)
      constant := (146888336365410044014830847423650029509899555320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree022.table
  base := (-1360616638478015441676092347977068906649/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-15763994976174840715599234169300000000000000)
      constant := (55073851624210363748426095942237309570424718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22852655431744591741/10000000000000000000)
  centralHi := (228526554317445917411/100000000000000000000)
  directionLo := (233904385494067120827/100000000000000000000)
  directionHi := (58476096373516780207/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree023.table
  base := (-11248588000839281070900433548346725609/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-45090510381826804239297211465394400000000000000)
      constant := (166520045659849865255604155809214525902292655500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree023.table
  base := (-11348410194210115124733638082786878948221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-66631318702308175646598085405200000000000000)
      constant := (249623932095505925602487792768723784403379811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233904385494067120827/100000000000000000000)
  centralHi := (58476096373516780207/25000000000000000000)
  directionLo := (239161320197288080191/100000000000000000000)
  directionHi := (3736895628082626253/1562500000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree024.table
  base := (-11614202605524727718966543868138047102487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-95030561554110234746183258322510800000000000000)
      constant := (374882427693244089055848205709209700858379911073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree024.table
  base := (-11703789690079315116001502763524858336677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-70206657499916988430799234133200000000000000)
      constant := (280864808113055901222870069368173587934280507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239161320197288080191/100000000000000000000)
  centralHi := (3736895628082626253/1562500000000000000)
  directionLo := (122152581433695409089/50000000000000000000)
  directionHi := (244305162867390818179/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree025.table
  base := (-11879980115786237355698784690819365392317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-99880102344566861013772093714232800000000000000)
      constant := (419275766124124501366127094135047149910420921643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree025.table
  base := (-11960247190385777670626726480411462547461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-73781996297525801215000382861200000000000000)
      constant := (313997765660237876207868817984771079232658651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122152581433695409089/50000000000000000000)
  centralHi := (244305162867390818179/100000000000000000000)
  directionLo := (249342912730269820111/100000000000000000000)
  directionHi := (15583932045641863757/6250000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree026.table
  base := (-12053851416450668962457115817877037486149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-104729643135023487281360929105954800000000000000)
      constant := (466196122656987481832475713901110675520349599971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree026.table
  base := (-3031413994375758196551617424983571883283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-19339333773783653499800382897300000000000000)
      constant := (87251353164072180698197977787011289709827853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249342912730269820111/100000000000000000000)
  centralHi := (15583932045641863757/6250000000000000000)
  directionLo := (254280875517541722929/100000000000000000000)
  directionHi := (25428087551754172293/10000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree027.table
  base := (-12142635325944094321624501502592360906293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-109579183925480113548949764497676800000000000000)
      constant := (515622876359835559830282312766802986943700306547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree027.table
  base := (-12206776237443413188355474018359537906421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-80932673892743426783402680317200000000000000)
      constant := (385872815850307197986756384671843780764716011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254280875517541722929/100000000000000000000)
  centralHi := (25428087551754172293/10000000000000000000)
  directionLo := (64781189003405990491/25000000000000000000)
  directionHi := (51824951202724792393/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree028.table
  base := (-1519024654985838503145489268900574839521/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-57214362357968369908269299944699400000000000000)
      constant := (283769144783300198434952617327997698862931655836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree028.table
  base := (-12209414800380954285152190787910805479469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-84508012690352239567603829045200000000000000)
      constant := (424587147954438857573316939519105030695852979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64781189003405990491/25000000000000000000)
  centralHi := (51824951202724792393/20000000000000000000)
  directionLo := (131939867652155034383/50000000000000000000)
  directionHi := (263879735304310068767/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree029.table
  base := (-1208758392263548105346500596376819214647/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-59639132753196683042063717640560400000000000000)
      constant := (310963550125604012756578772083903535498912498565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree029.table
  base := (-12138560876167119580975275429498290755631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-88083351487961052351804977773200000000000000)
      constant := (465137387804121818671301125865038275720811121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131939867652155034383/50000000000000000000)
  centralHi := (263879735304310068767/100000000000000000000)
  directionLo := (268550535708691789161/100000000000000000000)
  directionHi := (134275267854345894581/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree030.table
  base := (-373535580421830265013438871518179119799/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-62063903148424996175858135336421400000000000000)
      constant := (339388087026711734264897421938141162272869253136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree030.table
  base := (-11998501876841568195727104292521730096249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-91658690285569865136006126501200000000000000)
      constant := (507514064506160474284844594353819498217385959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268550535708691789161/100000000000000000000)
  centralHi := (134275267854345894581/50000000000000000000)
  directionLo := (273141475712821654627/100000000000000000000)
  directionHi := (68285368928205413657/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree031.table
  base := (-1175259935315201667784822714443489874639/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-64488673543653309309652553032282400000000000000)
      constant := (369037103161522459944957804425347844784084163405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree031.table
  base := (-5896461256496270772163248510017200658153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-47617014541589338960103637614600000000000000)
      constant := (275854519267432699564195836196972003746140023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273141475712821654627/100000000000000000000)
  centralHi := (68285368928205413657/25000000000000000000)
  directionLo := (5553130334495330027/2000000000000000000)
  directionHi := (277656516724766501351/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree032.table
  base := (-2297836782455635790572385376048984498991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-133826887877763244886893941456286800000000000000)
      constant := (799811466495073210627971144509812444739634190445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree032.table
  base := (-11524989724313913205840321306316318615287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-98809367880787490704408423957200000000000000)
      constant := (597715314120452826465783649248747252178831017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5553130334495330027/2000000000000000000)
  centralHi := (277656516724766501351/100000000000000000000)
  directionLo := (70524825772951726743/25000000000000000000)
  directionHi := (282099303091806906973/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree033.table
  base := (-5582831000719290673491567004537880013773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-69338214334109935577241388424004400000000000000)
      constant := (431989789254335234024889083690813351754868781467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree033.table
  base := (-11197425548220166838612855255298563513849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-102384706678396303488609572685200000000000000)
      constant := (645526878282274161895738014586645473197907559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70524825772951726743/25000000000000000000)
  centralHi := (282099303091806906973/100000000000000000000)
  directionLo := (286473196529859903059/100000000000000000000)
  directionHi := (14323659826492995153/5000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree034.table
  base := (-1078441789225121434775092805977959092781/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-71762984729338248711035806119865400000000000000)
      constant := (465285666018983511572084754371133241851900147495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree034.table
  base := (-10812569682426198401204049453862167244423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-105960045476005116272810721413200000000000000)
      constant := (695138562628077200245795837561218472557069593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286473196529859903059/100000000000000000000)
  centralHi := (14323659826492995153/5000000000000000000)
  directionLo := (5815626117803252801/2000000000000000000)
  directionHi := (290781305890162640051/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree035.table
  base := (-10347504066645797849067470412855386186481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-148375510249133123689660447631452800000000000000)
      constant := (999580520129257089455877870415575856670352891799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree035.table
  base := (-5186216611185152529768591402802826455869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-54767692136806964528505935070600000000000000)
      constant := (373272962324019371538216297537208556358985379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5815626117803252801/2000000000000000000)
  centralHi := (290781305890162640051/100000000000000000000)
  directionLo := (295026513012544233821/100000000000000000000)
  directionHi := (147513256506272116911/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree036.table
  base := (-9856687410491349183698254198360900582561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-153225051039589749957249283023174800000000000000)
      constant := (1071001799505879568419523136551591434969365046119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree036.table
  base := (-9878744830987429100909516267944460791181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-113110723071222741841213018869200000000000000)
      constant := (799745145725735502875008637671310686112281171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295026513012544233821/100000000000000000000)
  centralHi := (147513256506272116911/50000000000000000000)
  directionLo := (149605747638161892067/50000000000000000000)
  directionHi := (59842299055264756827/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree037.table
  base := (-9313488966164014241383891191492159686989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 817330000000000000000000000000000000000000000
      center := (4032130)
      previous := (3487306)
      next := (0)
      square := (141307140205493759811949946318000000000000000)
      linear := (-4272286265676929087157786984186400000000000000)
      constant := (30941366766260618036510190230489071312303328063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree037.table
  base := (-9332990413398704587893948050540920051257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-116686061868831554625414167597200000000000000)
      constant := (854732943496754894497300433206755107606773287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149605747638161892067/50000000000000000000)
  centralHi := (59842299055264756827/20000000000000000000)
  directionLo := (303338745350220844891/100000000000000000000)
  directionHi := (75834686337555211223/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree038.table
  base := (-1089902268323949064079020861567515129891/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-81462066310251501246213476903309400000000000000)
      constant := (610531436421707178163452840775081538311515596756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree038.table
  base := (-873644721394030629969994216190230492937/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-60130700333220183704807658162600000000000000)
      constant := (455753248264179153928017137842978904205510835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303338745350220844891/100000000000000000000)
  centralHi := (75834686337555211223/25000000000000000000)
  directionLo := (307410588555109347761/100000000000000000000)
  directionHi := (153705294277554673881/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree039.table
  base := (-8075002184841172462405946091067877421177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-167773673410959628760015789198340800000000000000)
      constant := (1299695298092003958711857101987515419465192789583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree039.table
  base := (-8090213121671941664280612570647376962019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-123836739464049180193816465053200000000000000)
      constant := (970063379583612849242861736352239944290900029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307410588555109347761/100000000000000000000)
  centralHi := (153705294277554673881/50000000000000000000)
  directionLo := (155714599091536150967/50000000000000000000)
  directionHi := (62285839636614460387/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree040.table
  base := (-230681608876138089758553848109854167077/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-86311607100708127513802312295031400000000000000)
      constant := (690362455740473467121414801565278875302478970928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree040.table
  base := (-7395231858782368495414605880603447701057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-127412078261657992978017613781200000000000000)
      constant := (1030401507980203552647145784857746984028365087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155714599091536150967/50000000000000000000)
  centralHi := (62285839636614460387/20000000000000000000)
  directionLo := (157698304529649210199/50000000000000000000)
  directionHi := (315396609059298420399/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree041.table
  base := (-664048143903424845742674812644264245527/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-88736377495936440647596729990892400000000000000)
      constant := (732074593337556594543081153285111724827763216165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree041.table
  base := (-6652314630884443120119086422867208428203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-130987417059266805762218762509200000000000000)
      constant := (1092519089764931618442505505195086336582099573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157698304529649210199/50000000000000000000)
  centralHi := (315396609059298420399/100000000000000000000)
  directionLo := (319314729587058856193/100000000000000000000)
  directionHi := (159657364793529428097/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree042.table
  base := (-731466402664413338450574152607799965219/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-91161147891164753781391147686753400000000000000)
      constant := (774982974406462751061389243789592989445527810004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree042.table
  base := (-5862158736497611328210196574441741032363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-134562755856875618546419911237200000000000000)
      constant := (1156414584605367590879237038853458194059510133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319314729587058856193/100000000000000000000)
  centralHi := (159657364793529428097/50000000000000000000)
  directionLo := (323185352478123795539/100000000000000000000)
  directionHi := (16159267623906189777/5000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree043.table
  base := (-2508089974954414731491249589529343636779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-93585918286393066915185565382614400000000000000)
      constant := (819086662801763030817225778453155381791800253741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree043.table
  base := (-2512681781486026650658308843880320188391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-69069047327242215665310529982600000000000000)
      constant := (611043334227427460968061314362668372703844281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323185352478123795539/100000000000000000000)
  centralHi := (16159267623906189777/5000000000000000000)
  directionLo := (327010164339828612323/100000000000000000000)
  directionHi := (81752541084957153081/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree044.table
  base := (-258397538262801210488572307625744843413/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-96010688681621380048979983078475400000000000000)
      constant := (864384852614278012717314663073475799027144280216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree044.table
  base := (-1035611083999444137943496692420540199017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-35428358363023311028705552173300000000000000)
      constant := (322383550794961096254603213165643026700371447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327010164339828612323/100000000000000000000)
  centralHi := (81752541084957153081/25000000000000000000)
  directionLo := (330790754264254360933/100000000000000000000)
  directionHi := (165395377132127180467/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree045.table
  base := (-1603366023903466226228042312864540615141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-98435459076849693182774400774336400000000000000)
      constant := (910876850050767172822580614143582022570399183939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree045.table
  base := (-3213843938224542934480300891371252755067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-145288772249702056899023357421200000000000000)
      constant := (1358756210452562656188638035134960902664056997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330790754264254360933/100000000000000000000)
  centralHi := (165395377132127180467/50000000000000000000)
  directionLo := (167264310771804300593/50000000000000000000)
  directionHi := (334528621543608601187/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree046.table
  base := (-2233689264968646067521606116084084799583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-201720458944156012633137636940394800000000000000)
      constant := (1917124115669706508087005930776322481391800258457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree046.table
  base := (-279992883522227652015536100405033889997/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-37216027761827717420806126537300000000000000)
      constant := (357437962327491743735295693583210560273993254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167264310771804300593/50000000000000000000)
  centralHi := (334528621543608601187/100000000000000000000)
  directionLo := (169112591309029611529/50000000000000000000)
  directionHi := (338225182618059223059/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree047.table
  base := (-607786160815520296346015581550483060487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 321715000000000000000000000000000000000000000
      center := (1587115)
      previous := (1372663)
      next := (0)
      square := (55620895612800735245129234189000000000000000)
      linear := (-2197553188666091903199217790767200000000000000)
      constant := (21434892803794805051290322168025447268439084959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree047.table
  base := (-1221068972557092647702774457881568235143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 470000000000000000000000000000000000000000
      center := (2300)
      previous := (2024)
      next := (0)
      square := (81257699945654836004571562000000000000000)
      linear := (-3243392549891908137604801167600000000000000)
      constant := (31968519082214855046650959279679566292948279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169112591309029611529/50000000000000000000)
  centralHi := (338225182618059223059/100000000000000000000)
  directionLo := (341881777347334072347/100000000000000000000)
  directionHi := (85470444336833518087/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree048.table
  base := (-152673970787382338484443460507577476561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-211419540525069265168315307723838800000000000000)
      constant := (2115020238442075096339787053684412764294004872119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree048.table
  base := (-3937573806555797223739055143360378637/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-39003697160632123812906700901300000000000000)
      constant := (394265307930317117454880749190283169235908670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (341881777347334072347/100000000000000000000)
  centralHi := (85470444336833518087/25000000000000000000)
  directionLo := (69099934936966389857/20000000000000000000)
  directionHi := (172749837342415974643/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree049.table
  base := (954753757894884330414210853712249614459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-216269081315525891435904143115560800000000000000)
      constant := (2217544298157586831122914788204638842016327365539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree049.table
  base := (95051318564491104375118055752068940427/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-79795063720068654017913976166600000000000000)
      constant := (826686909864839098067886940202181601447016215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69099934936966389857/20000000000000000000)
  centralHi := (172749837342415974643/50000000000000000000)
  directionLo := (87270019455594437039/25000000000000000000)
  directionHi := (349080077822377748157/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree050.table
  base := (1053246946094300709116745625582612944089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-110559311052991258851746489253641400000000000000)
      constant := (1161225723276489156952673093486952517039091370769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree050.table
  base := (2102771582021486133443215277876583651937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-163165466237746120820029101061200000000000000)
      constant := (1731457701728480810453891406108829373287128833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87270019455594437039/25000000000000000000)
  centralHi := (349080077822377748157/100000000000000000000)
  directionLo := (70524825772951726743/20000000000000000000)
  directionHi := (88156032216189658429/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree051.table
  base := (3302359639745899962632271478424727951769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-225968162896439143971081813899004800000000000000)
      constant := (2429741118745587714852817240925572566718231620049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree051.table
  base := (41238669481655158723771339467825871289/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-41685201258838733401057562447300000000000000)
      constant := (452828120754308529886710228451488546993548020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70524825772951726743/20000000000000000000)
  centralHi := (88156032216189658429/25000000000000000000)
  directionLo := (178066456542762778913/50000000000000000000)
  directionHi := (356132913085525557827/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree052.table
  base := (4542190189177878629135876084498049932151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-230817703686895770238670649290726800000000000000)
      constant := (2539412828422316818272815060060109927258866414271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree052.table
  base := (453932551997992516538972972563054652919/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-85158071916481873194215699258600000000000000)
      constant := (946468912152073129633327766461158938641490355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178066456542762778913/50000000000000000000)
  centralHi := (356132913085525557827/100000000000000000000)
  directionLo := (44950932851126526141/12500000000000000000)
  directionHi := (359607462809012209129/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree053.table
  base := (5825847095352170900755784287917382878977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-235667244477352396506259484682448800000000000000)
      constant := (2651466156908333486801617801923343903829354804217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree053.table
  base := (1455833858016302315054555904261547230533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-43472870657643139793158136811300000000000000)
      constant := (494083358481362787219584532829913757832247397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44950932851126526141/12500000000000000000)
  centralHi := (359607462809012209129/100000000000000000000)
  directionLo := (90762190239482327491/25000000000000000000)
  directionHi := (72609752191585861993/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree054.table
  base := (7153211167623158868639637626034911986679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-240516785267809022773848320074170800000000000000)
      constant := (2765900743756703303763088963388853524072067684159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree054.table
  base := (715100979377490988722440335214474095131/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-88733410714090685978416847986600000000000000)
      constant := (1030749530578705143488337057936843866380721895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90762190239482327491/25000000000000000000)
  centralHi := (72609752191585861993/20000000000000000000)
  directionLo := (91614436075271556817/25000000000000000000)
  directionHi := (366457744301086227269/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree055.table
  base := (8524179791019171472038196280310794640663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-245366326058265649041437155465892800000000000000)
      constant := (2882716278647335524297324492587356260599516432223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree055.table
  base := (1704450206986571704179897038535005569989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-181042160225790184741034844701200000000000000)
      constant := (2148434490467504517288814583306619136520528505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91614436075271556817/25000000000000000000)
  centralHi := (366457744301086227269/100000000000000000000)
  directionLo := (369835306431650591457/100000000000000000000)
  directionHi := (184917653215825295729/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree056.table
  base := (9938664620147006192651796215798649281737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-250215866848722275309025990857614800000000000000)
      constant := (3001912494413071311411481491217826027064535778177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree056.table
  base := (2484243819802852740692618848830225476539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-46154374755849749381308998357300000000000000)
      constant := (559284884143231518445083172609865968077674651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (369835306431650591457/100000000000000000000)
  centralHi := (184917653215825295729/50000000000000000000)
  directionLo := (373182300502777719023/100000000000000000000)
  directionHi := (23323893781423607439/6250000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree057.table
  base := (2849147398488874981088737530893545981137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-127532703819589450788307413124668400000000000000)
      constant := (1561744580518044280340950322237055692332044011154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree057.table
  base := (2279022084256219505353448836160393065359/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-188192837821007810309437142157200000000000000)
      constant := (2327614040193002157914699520589791541406890155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373182300502777719023/100000000000000000000)
  centralHi := (23323893781423607439/6250000000000000000)
  directionLo := (37649954174434009457/10000000000000000000)
  directionHi := (376499541744340094571/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree058.table
  base := (12897889226715130994755504038743647092553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-259914948429635527844203661641058800000000000000)
      constant := (3247446080479617425299145719315743876789178470913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree058.table
  base := (12896594473984221236753972474168823203083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-191768176618616623093638290885200000000000000)
      constant := (2419857864398101417071631049421038930455610347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37649954174434009457/10000000000000000000)
  centralHi := (376499541744340094571/100000000000000000000)
  directionLo := (1483546131960125331/390625000000000000)
  directionHi := (379787809781792084737/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree059.table
  base := (14442507136782012076900145460565099054599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-264764489220092154111792497032780800000000000000)
      constant := (3373783082238744611076143337389667287918092982479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree059.table
  base := (14441374147612932586055129029772085299307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-195343515416225435877839439613200000000000000)
      constant := (2513870891471259211690881028411566536426169163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1483546131960125331/390625000000000000)
  centralHi := (379787809781792084737/100000000000000000000)
  directionLo := (47880981346982136987/12500000000000000000)
  directionHi := (383047850775857095897/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree060.table
  base := (2003799347507725830545365998539771358083/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-134807015005274390189690666212251400000000000000)
      constant := (1751250009755127504471130869620294367596709280172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree060.table
  base := (500918863396789960440176235408870856999/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-49729713553458562165510147085300000000000000)
      constant := (652413255052630103986899257100145565784886328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47880981346982136987/12500000000000000000)
  centralHi := (383047850775857095897/100000000000000000000)
  directionLo := (386280379399673733471/100000000000000000000)
  directionHi := (12071261856239804171/3125000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree061.table
  base := (17661510359692308475200539845292965766341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-274463570801005406646970167816224800000000000000)
      constant := (3633596765895379886955391494915012508926272911261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree061.table
  base := (17660643530285929671016327375873856880463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-202494193011443061446241737069200000000000000)
      constant := (2707204163610109541850066398260505349848942767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386280379399673733471/100000000000000000000)
  centralHi := (12071261856239804171/3125000000000000000)
  directionLo := (97371520167060553633/25000000000000000000)
  directionHi := (389486080668242214533/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree062.table
  base := (9667908943713086752868713094712482921321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-139656555795731016457279501603973400000000000000)
      constant := (1883536606280652349369173010914199808564508183841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree062.table
  base := (19335059989636728260734698328570119917887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-206069531809051874230442885797200000000000000)
      constant := (2806524246867229164284616638238211394898612383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97371520167060553633/25000000000000000000)
  centralHi := (389486080668242214533/100000000000000000000)
  directionLo := (392665611633436879151/100000000000000000000)
  directionHi := (24541600727089804947/6250000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree063.table
  base := (21053286375606693478335331760915403576283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-284162652381918659182147838599668800000000000000)
      constant := (3902929265797606052058328061846232151178512522243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree063.table
  base := (10526311946308077144187871249669631890447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-104822435303330343507322017262600000000000000)
      constant := (1453806602834379168548305470741320216845997423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392665611633436879151/100000000000000000000)
  centralHi := (24541600727089804947/6250000000000000000)
  directionLo := (395819602956465103149/100000000000000000000)
  directionHi := (7916392059129302063/2000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree064.table
  base := (22813889141566261087889124003509857937219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-289012193172375285449736673991390800000000000000)
      constant := (4041164844912668499644215776397357435094960659499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree064.table
  base := (22813310207013819286175257228158770276571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-213220209404269499798845183253200000000000000)
      constant := (3010470984718544312160758184317802723540945339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395819602956465103149/100000000000000000000)
  centralHi := (7916392059129302063/2000000000000000000)
  directionLo := (398948660368431712179/100000000000000000000)
  directionHi := (19947433018421585609/5000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree065.table
  base := (6154400802201333462005105758920161767869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-146930866981415955858662754691556400000000000000)
      constant := (2090889940211388634286280046468035047051219536298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree065.table
  base := (24617097409476908935754689790018680652617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-216795548201878312583046331981200000000000000)
      constant := (3115097536471500722647760143774151265561630953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398948660368431712179/100000000000000000000)
  centralHi := (19947433018421585609/5000000000000000000)
  directionLo := (50256670753573673281/12500000000000000000)
  directionHi := (402053366028589386249/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree066.table
  base := (211715270331888864828445176037877392119/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-298711274753288537984914344774834800000000000000)
      constant := (4324774312493164754215873823936422027116537799875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree066.table
  base := (26463966992917388422827073186195665718321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-220370886999487125367247480709200000000000000)
      constant := (3221492820045470099652856909751506225571771089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50256670753573673281/12500000000000000000)
  centralHi := (402053366028589386249/100000000000000000000)
  directionLo := (81026855957780188821/20000000000000000000)
  directionHi := (202567139894450472053/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree067.table
  base := (221517881645693011971057530670638178577/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-151780407771872582126251590083278400000000000000)
      constant := (2235074044797977285191274450472508193951133172288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree067.table
  base := (177211894019319116782790245996361490807/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-55986556449273984537862157359300000000000000)
      constant := (832414200071471751861942009702838501327706520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81026855957780188821/20000000000000000000)
  centralHi := (202567139894450472053/50000000000000000000)
  directionLo := (40819194037269289287/10000000000000000000)
  directionHi := (408191940372692892871/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree068.table
  base := (30287228712170583142616155177727851591009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-308410356334201790520092015558278800000000000000)
      constant := (4617901167354824578238214119617467928281253728089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree068.table
  base := (30286891874634554093896687696480163846719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-227521564594704750935649778165200000000000000)
      constant := (3439589446961783771357776064699124681937402271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40819194037269289287/10000000000000000000)
  centralHi := (408191940372692892871/100000000000000000000)
  directionLo := (25701679154651722091/6250000000000000000)
  directionHi := (411226866474427553457/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree069.table
  base := (32263215737878373554504510827987818170707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-313259897124658416787680850950000800000000000000)
      constant := (4768033507550409295848255644283481048674216623547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree069.table
  base := (4032865214776314127967529593348884726961/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-57774225848078390929962731723300000000000000)
      constant := (887822683518673539888293242497615372723713698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25701679154651722091/6250000000000000000)
  centralHi := (411226866474427553457/100000000000000000000)
  directionLo := (414239557786951663057/100000000000000000000)
  directionHi := (207119778893475831529/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree070.table
  base := (17141119521208334236413743976729251621723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-159054718957557521527634843170861400000000000000)
      constant := (2460272538632038420261893872228658441143536580483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree070.table
  base := (17140991225791863861205436132832721564371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-117336121094961188252026037810600000000000000)
      constant := (1832380319632300299054490893709427481935695539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414239557786951663057/100000000000000000000)
  centralHi := (207119778893475831529/50000000000000000000)
  directionLo := (83446099192396492573/20000000000000000000)
  directionHi := (208615247980991231433/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree071.table
  base := (1817214462475362692736482940486977086339/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-161479489352785834661429260866722400000000000000)
      constant := (2537717924070413681667658210566575826333165830190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree071.table
  base := (36344065368458989917601200485150091871987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-238247580987531189288253224349200000000000000)
      constant := (3779999143299296971951675484150896552945219283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83446099192396492573/20000000000000000000)
  centralHi := (208615247980991231433/50000000000000000000)
  directionLo := (210100072754529562961/50000000000000000000)
  directionHi := (420200145509059125923/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree072.table
  base := (38449358282118129761109087362997153197801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-327808519496028295590447357125166800000000000000)
      constant := (5232705795754738775595004788410411913925687157921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree072.table
  base := (19224581489888858607483554571655462527511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-120911459892570001036227186538600000000000000)
      constant := (1948503114817726436286073958099986916723271799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210100072754529562961/50000000000000000000)
  centralHi := (420200145509059125923/100000000000000000000)
  directionLo := (211574477318855180229/50000000000000000000)
  directionHi := (423148954637710360459/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree073.table
  base := (40597439181824221276731477290277272827843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-332658060286484921858036192516888800000000000000)
      constant := (5392354899062691681325119590858629496581409401003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree073.table
  base := (4059726884291514890914175954579040389121/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-122699129291374407428327760902600000000000000)
      constant := (2007890942020655101786121868445125501097841445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211574477318855180229/50000000000000000000)
  centralHi := (423148954637710360459/100000000000000000000)
  directionLo := (85215471209432306567/20000000000000000000)
  directionHi := (106519339011790383209/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree074.table
  base := (42788525953298157695457907996715930798561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 817330000000000000000000000000000000000000000
      center := (4032130)
      previous := (3487306)
      next := (0)
      square := (141307140205493759811949946318000000000000000)
      linear := (-9121827056133555354746622375908400000000000000)
      constant := (150118463241461910186444359183501183171958786213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree074.table
  base := (42788377414860023601300397689223684322147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-248973597380357627640856670533200000000000000)
      constant := (4136326094272357088521959064628295118667622723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85215471209432306567/20000000000000000000)
  centralHi := (106519339011790383209/25000000000000000000)
  directionLo := (428985767667520942539/100000000000000000000)
  directionHi := (21449288383376047127/5000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree075.table
  base := (22511306715217314000506287242336797047291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-171178570933699087196606931650166400000000000000)
      constant := (2859395251373004101529559440758944047023450706211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree075.table
  base := (4502248392600888102139631692033622673151/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-126274468088983220212528909630600000000000000)
      constant := (2129319424896269741842380362208511362424952795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428985767667520942539/100000000000000000000)
  centralHi := (21449288383376047127/5000000000000000000)
  directionLo := (215937296678019968303/50000000000000000000)
  directionHi := (431874593356039936607/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree076.table
  base := (47299697161098320177166234208763501622889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-347206682657854800660802698692054800000000000000)
      constant := (5885576974034648367897321172848064889291312705569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree076.table
  base := (11824896067920022605682380330448239628463/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-64031068743893813302314741997300000000000000)
      constant := (1095680035383653916685297106318760161339274767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215937296678019968303/50000000000000000000)
  centralHi := (431874593356039936607/100000000000000000000)
  directionLo := (54343027943966374067/12500000000000000000)
  directionHi := (434744223551730992537/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree077.table
  base := (24809886653952130255176504339055055919737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-176028111724155713464195767041888400000000000000)
      constant := (3027371271097647343660702802876184564763050976177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree077.table
  base := (9923934983771849774831282246395839349831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-259699613773184065993460116717200000000000000)
      constant := (4508569961694156821616345955549842045618883395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54343027943966374067/12500000000000000000)
  centralHi := (434744223551730992537/100000000000000000000)
  directionLo := (218797517945673946507/50000000000000000000)
  directionHi := (87519007178269578603/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree078.table
  base := (12995709640699976268972006657445251962069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-178452882119384026597990184737749400000000000000)
      constant := (3113143598611997997072655121331135185617568132698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree078.table
  base := (51982752826037041966518125397048688104557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-263274952570792878777661265445200000000000000)
      constant := (4636188303552468872780401390731680552022966413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218797517945673946507/50000000000000000000)
  centralHi := (87519007178269578603/20000000000000000000)
  directionLo := (110106848947369825029/25000000000000000000)
  directionHi := (440427395789479300117/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree079.table
  base := (13597222518382176724641846818632613241403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-180877652514612339731784602433610400000000000000)
      constant := (3200105465247591683636917243959547003976409763526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree079.table
  base := (54388815374301034317716361314908197583403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-266850291368401691561862414173200000000000000)
      constant := (4765575161324374250474299580593432208461737227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110106848947369825029/25000000000000000000)
  centralHi := (440427395789479300117/100000000000000000000)
  directionLo := (17729666279411138281/4000000000000000000)
  directionHi := (221620828492639228513/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree080.table
  base := (28418962690161034319224335496871845203033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-183302422909840652865579020129471400000000000000)
      constant := (3288256867285109468175357165781687581387241358993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree080.table
  base := (7104732538512631171780523110413827742291/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-67606407541502626086515890725300000000000000)
      constant := (1224182632506840653672835926925808290965441638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17729666279411138281/4000000000000000000)
  centralHi := (221620828492639228513/50000000000000000000)
  directionLo := (446038162058144801581/100000000000000000000)
  directionHi := (223019081029072400791/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree081.table
  base := (29664971180698300365161646881912174650249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-185727193305068965999373437825332400000000000000)
      constant := (3377597801516286497770310812634545777515485656129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree081.table
  base := (29664942842164865580891384874605554118241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-137000484481809658565132355814600000000000000)
      constant := (2514827202684554908042131742323603669047194369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446038162058144801581/100000000000000000000)
  centralHi := (223019081029072400791/50000000000000000000)
  directionLo := (448817242914485676201/100000000000000000000)
  directionHi := (224408621457242838101/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree082.table
  base := (61864939186031611341925832246962283571393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-376303927400594558266335711042386800000000000000)
      constant := (6936256530345924655539074024746481427956204570553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree082.table
  base := (30932444914275323378358278814528637026581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-138788153880614064957232930178600000000000000)
      constant := (2582173391825392887162396071588493759191717429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448817242914485676201/100000000000000000000)
  centralHi := (224408621457242838101/50000000000000000000)
  directionLo := (451579221247516038739/100000000000000000000)
  directionHi := (22578961062375801937/5000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree083.table
  base := (32221457137086105126584826806157961729639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-190576734095525592266962273217054400000000000000)
      constant := (3559848255865998370839406460916253671383797622319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree083.table
  base := (64442871297370264200867895292122386991601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-281151646558836942698667009085200000000000000)
      constant := (5300807661683934177317315247305898352864446609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451579221247516038739/100000000000000000000)
  centralHi := (22578961062375801937/5000000000000000000)
  directionLo := (454324408971899328481/100000000000000000000)
  directionHi := (227162204485949664241/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree084.table
  base := (67063866261650147173185462576956858957257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-386003008981507810801513381825830800000000000000)
      constant := (7305515543065379400721964372406864553266678996097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree084.table
  base := (33531914423045544293434737487953508652367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-142363492678222877741434078906600000000000000)
      constant := (2719518518359509129405729207093289300613078703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454324408971899328481/100000000000000000000)
  centralHi := (227162204485949664241/50000000000000000000)
  directionLo := (457053108634891834821/100000000000000000000)
  directionHi := (228526554317445917411/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree085.table
  base := (69727793970240826117086973798477986046013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-390852549771964437069102217217552800000000000000)
      constant := (7493713620782978889234118078353587545639454879573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree085.table
  base := (69727761400904392994108364201004885618083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-288302324154054568267069306541200000000000000)
      constant := (5579034906383994541039587675972019792330345347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457053108634891834821/100000000000000000000)
  centralHi := (228526554317445917411/50000000000000000000)
  directionLo := (459765613805524646221/100000000000000000000)
  directionHi := (229882806902762323111/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree086.table
  base := (72434696381883682119375786446697693186413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-395702090562421063336691052609274800000000000000)
      constant := (7684290741806056873431246050255706674616588467973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree086.table
  base := (72434668034985120609288386616566543470051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-291877662951663381051270455269200000000000000)
      constant := (5720801268631506473501131779103195494525342659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (459765613805524646221/100000000000000000000)
  centralHi := (229882806902762323111/50000000000000000000)
  directionLo := (231231104721620136763/50000000000000000000)
  directionHi := (462462209443240273527/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree087.table
  base := (37592286308243360177394735582191018589407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-200275815676438844802139944000498400000000000000)
      constant := (3938623451736554334915190422491497135327616086247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree087.table
  base := (75184547947941049110823422394186848680943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-295453001749272193835471603997200000000000000)
      constant := (5864336121693487637087706984879158748736203087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231231104721620136763/50000000000000000000)
  centralHi := (462462209443240273527/100000000000000000000)
  directionLo := (23257158612364711613/5000000000000000000)
  directionHi := (465143172247294232261/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree088.table
  base := (15595484382563321197006302439996697822049/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-405401172143334315871868723392718800000000000000)
      constant := (8072582103482072564646998365024364669071563219645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree088.table
  base := (77977400448145252075610061930260414744997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-299028340546881006619672752725200000000000000)
      constant := (6009639464042134151330677861485545256171698373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23257158612364711613/5000000000000000000)
  centralHi := (465143172247294232261/100000000000000000000)
  directionLo := (93561754197626848331/20000000000000000000)
  directionHi := (58476096373516780207/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree089.table
  base := (80813243612045068135892877221563774237093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-410250712933790942139457558784440800000000000000)
      constant := (8270296339840572148536714717315124362509651920253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree089.table
  base := (80813224937547030197386212148174125263141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-302603679344489819403873901453200000000000000)
      constant := (6156711294356352021462511445316116642706278469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93561754197626848331/20000000000000000000)
  centralHi := (58476096373516780207/12500000000000000000)
  directionLo := (235229633410940184739/50000000000000000000)
  directionHi := (470459266821880369479/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree090.table
  base := (8369203714358210354549361616474409561439/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-207550126862123784203523197088081400000000000000)
      constant := (4235194805411537105122605122693317039586742350595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree090.table
  base := (10461502612326666872834002806671605037647/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5522500000000000000000000000000000000000000
      center := (27025)
      previous := (23782)
      next := (0)
      square := (954777974361444323053715853500000000000000)
      linear := (-76544754535524658047018762545300000000000000)
      constant := (1576387902873227685840277686601875151056324446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235229633410940184739/50000000000000000000)
  centralHi := (470459266821880369479/100000000000000000000)
  directionLo := (473094913588947630597/100000000000000000000)
  directionHi := (236547456794473815299/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree091.table
  base := (86613802012877877735758518813495588014101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-419949794514704194674635229567884800000000000000)
      constant := (8672861914934000209780813666445186391120791130221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree091.table
  base := (86613787883101573701306424034313977629867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-309754356939707444972276198909200000000000000)
      constant := (6456160414461642429685549963754999576584376203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473094913588947630597/100000000000000000000)
  centralHi := (236547456794473815299/50000000000000000000)
  directionLo := (475715958097777526643/100000000000000000000)
  directionHi := (118928989524444381661/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree092.table
  base := (89578537790919480288952587064465923445767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-424799335305160820942224064959606800000000000000)
      constant := (8877713250875963195478133800291473352876736345807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree092.table
  base := (44789262751203343961002773033327368191779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-156664847868658128878238673818600000000000000)
      constant := (3304268851202059253180561513353820156335639811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475715958097777526643/100000000000000000000)
  centralHi := (118928989524444381661/25000000000000000000)
  directionLo := (478322640394576160383/100000000000000000000)
  directionHi := (3736895628082626253/781250000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree093.table
  base := (92586244105186791322555507753860703147657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-429648876095617447209812900351328800000000000000)
      constant := (9084943617522417249877923434960287883463595634497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree093.table
  base := (18517246683852300542292644222523816317689/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-316905034534925070540678496365200000000000000)
      constant := (6762683474575315783960156611395375551228875005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478322640394576160383/100000000000000000000)
  centralHi := (3736895628082626253/781250000000000000)
  directionLo := (120228798504973325829/25000000000000000000)
  directionHi := (480915194019893303317/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree094.table
  base := (95636920631864515417115847862950366403001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 643430000000000000000000000000000000000000000
      center := (3174230)
      previous := (2745326)
      next := (0)
      square := (111241791225601470490258468378000000000000000)
      linear := (-9244647167788810073987270973256400000000000000)
      constant := (197756447104129909318745014539991415425468293343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree094.table
  base := (47818455670300188963260202619885450592481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235000000000000000000000000000000000000000
      center := (1150)
      previous := (1012)
      next := (0)
      square := (40628849972827418002285781000000000000000)
      linear := (-3409365673750360460902974947800000000000000)
      constant := (73602103514126087908578855210334616177846607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120228798504973325829/25000000000000000000)
  centralHi := (480915194019893303317/100000000000000000000)
  directionLo := (241746923126409314031/50000000000000000000)
  directionHi := (483493846252818628063/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree095.table
  base := (19746113417827134941163067205867804566157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-439347957676530699744990571134772800000000000000)
      constant := (9506541439138780018863830207938679255062056364985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree095.table
  base := (49365279505711434526799099843873578051033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (54050)
      previous := (47564)
      next := (0)
      square := (1909555948722888646107431707000000000000000)
      linear := (-162027856065071348054540396910600000000000000)
      constant := (3538140234549215981384697287237116733914731897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241746923126409314031/50000000000000000000)
  centralHi := (483493846252818628063/100000000000000000000)
  directionLo := (486058818343517779417/100000000000000000000)
  directionHi := (243029409171758889709/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree096.table
  base := (20373436646281231917527403627363354807597/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-444197498466987326012579406526494800000000000000)
      constant := (9720908892513733788205630016338669279520525236185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree096.table
  base := (101867176209517034818772785377649358236043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-327631050927751508893281942549200000000000000)
      constant := (7235731690396188703775005449158427432343418987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486058818343517779417/100000000000000000000)
  centralHi := (243029409171758889709/50000000000000000000)
  directionLo := (488610325734781636357/100000000000000000000)
  directionHi := (244305162867390818179/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree097.table
  base := (52523384422165430114427216023782969522697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (74594405)
      previous := (64515161)
      next := (0)
      square := (2614182093801634556521074006883000000000000000)
      linear := (-224523519628721976140084120959108400000000000000)
      constant := (4968827686685380749055468203086443627575947974337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree097.table
  base := (105046762740921738419788125222937959438749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-331206389725360321677483091277200000000000000)
      constant := (7396951393792662335227061427899869952400196541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell029.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488610325734781636357/100000000000000000000)
  centralHi := (244305162867390818179/50000000000000000000)
  directionLo := (767419653551900999/156250000000000000)
  directionHi := (491148578273216639361/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree098.table
  base := (108269323740529915258621378303001580408527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (149188810)
      previous := (129030322)
      next := (0)
      square := (5228364187603269113042148013766000000000000000)
      linear := (-453896580047900578547757077309938800000000000000)
      constant := (10156780881143203774831084597888437842346615079767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree098.table
  base := (108269318436024230946701256461493748579343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (108100)
      previous := (95128)
      next := (0)
      square := (3819111897445777292214863414000000000000000)
      linear := (-334781728522969134461684240005200000000000000)
      constant := (7559939578913178294783498505957039690611768687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell029.Kernel098
