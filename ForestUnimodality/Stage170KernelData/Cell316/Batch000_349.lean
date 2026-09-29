import ForestUnimodality.FiniteKernelDegreeCertificate
import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell316.Parameters
import ForestUnimodality.BinomialMassData.Q467_742.Batch000_049
import ForestUnimodality.BinomialMassData.Q467_742.Batch050_099
import ForestUnimodality.BinomialMassData.Q467_742.Batch100_149
import ForestUnimodality.BinomialMassData.Q236_371.Batch000_049
import ForestUnimodality.BinomialMassData.Q236_371.Batch050_099
import ForestUnimodality.BinomialMassData.Q236_371.Batch100_149

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree000.table
  base := (7392610454467558345754696387/500000000000000000000000000)
  polynomial :=
    { denominator := 185500000000000000000000000000000000000000
      center := (467)
      previous := (0)
      next := (275)
      square := (1975892122984580075335803148000000000000)
      linear := (-5367484269551326606442764827500000000000)
      constant := (2742658478607464146274992359577000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree000.table
  base := (7392610454467558345754696387/500000000000000000000000000)
  polynomial :=
    { denominator := 92750000000000000000000000000000000000000
      center := (236)
      previous := (0)
      next := (135)
      square := (987946061492290037667901574000000000000)
      linear := (-2683742134775663303221382413750000000000)
      constant := (1371329239303732073137496179788500000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree000.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel000

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree001.table
  base := (122870026672855953237511233616284048720947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-58281565708746821323441716422370000000000000)
      constant := (16942827044531785834655318991680037749999866027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree001.table
  base := (122603980210299385102833845687712620149519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-58479154921045279330975296737170000000000000)
      constant := (16906601542033450286191423198473212749999944679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree001.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel001

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (48111508724453423913/100000000000000000000)
  directionHi := (24055754362226711957/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree002.table
  base := (25541768886736501047769803533916210921891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-19184099534355699806769529456172500000000000)
      constant := (3533935238823115968181074957840633687499999131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree002.table
  base := (50863639061111047104739124484573345696413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-38565788281009857621072639227145000000000000)
      constant := (7038121822073368615465527671536879874999981733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree002.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel002

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48111508724453423913/100000000000000000000)
  centralHi := (24055754362226711957/50000000000000000000)
  directionLo := (68039948144353518831/100000000000000000000)
  directionHi := (4252496759022094927/6250000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree003.table
  base := (85004741855911950196565501274495645383837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-95191230566098777130714519227010000000000000)
      constant := (11827604093835724741312263459966070126276708517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree003.table
  base := (84458861945773723314398209498262940855663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-95783998202994151153315260171410000000000000)
      constant := (11754398979733241072493053451172449442314310983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree003.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel003

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68039948144353518831/100000000000000000000)
  centralHi := (4252496759022094927/6250000000000000000)
  directionLo := (41665788769773319197/50000000000000000000)
  directionHi := (16666315507909327679/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree004.table
  base := (552820851191700767926844920319786008533/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-28411515748693688758587730157332500000000000)
      constant := (2483202431320524547350881580458606312015700896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree004.table
  base := (70158102268271345855365674941806673077593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-114436419843968587064485241888530000000000000)
      constant := (9852890675801871115925786171567772289072978113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree004.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel004

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41665788769773319197/50000000000000000000)
  centralHi := (16666315507909327679/20000000000000000000)
  directionLo := (96223017448906847827/100000000000000000000)
  directionHi := (24055754362226711957/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree005.table
  base := (14728289212776747441708499461744886461901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-33025223855862683234496830507912500000000000)
      constant := (2094846343174403162682731550073684167502515541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree005.table
  base := (58288011852360051018963253718236837402437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-133088841484943022975655223605650000000000000)
      constant := (8297807272015860081959670309584836536908831117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree005.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel005

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96223017448906847827/100000000000000000000)
  centralHi := (24055754362226711957/25000000000000000000)
  directionLo := (5379030200397602719/5000000000000000000)
  directionHi := (107580604007952054381/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree006.table
  base := (24521995878319597858974099452464471729363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-75277863926063355420811861716985000000000000)
      constant := (3554966420163669691764373485589817353301252683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree006.table
  base := (48421011517106187012893487674588206026083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-151741263125917458886825205322770000000000000)
      constant := (7030296342332319204251091427591355265636090203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree006.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel006

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5379030200397602719/5000000000000000000)
  centralHi := (107580604007952054381/100000000000000000000)
  directionLo := (117848647130372046337/100000000000000000000)
  directionHi := (58924323565186023169/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree007.table
  base := (40810238184012157196873577647022653385193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (495020)
      previous := (0)
      next := (291500)
      square := (2094445650363654879855951336880000000000000)
      linear := (-24144365754400384106465732119470000000000000)
      constant := (868170726951939901086845885314451433513049959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree007.table
  base := (20102948562079620722168220207973849755501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (250160)
      previous := (0)
      next := (143100)
      square := (1047222825181827439927975668440000000000000)
      linear := (-12170977483349421056999656217135000000000000)
      constant := (428715556996038971895708618589649807742416163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree007.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel007

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117848647130372046337/100000000000000000000)
  centralHi := (58924323565186023169/50000000000000000000)
  directionLo := (31822771821254533709/25000000000000000000)
  directionHi := (127291087285018134837/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree008.table
  base := (33929446483513081015640449444249781200623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-187465392709478666648896526238610000000000000)
      constant := (5242295465470213855783113516337624134234950343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree008.table
  base := (33354408206472348954313038272102481010151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-189046106407866330709165168757010000000000000)
      constant := (5173295179907741693950919328534297588718193791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree008.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel008

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31822771821254533709/25000000000000000000)
  centralHi := (127291087285018134837/100000000000000000000)
  directionLo := (68039948144353518831/50000000000000000000)
  directionHi := (136079896288707037663/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree009.table
  base := (14084579086641044096523239697372010348559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-102960112569077322276266463820465000000000000)
      constant := (2286619076422783712601326675180623376386009319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree009.table
  base := (27629839628908940973791668163728269550411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-207698528048840766620335150474130000000000000)
      constant := (4511548156716575032074007176577682749188120451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree009.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel009

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68039948144353518831/50000000000000000000)
  centralHi := (136079896288707037663/100000000000000000000)
  directionLo := (7216726308668013587/5000000000000000000)
  directionHi := (144334526173360271741/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree010.table
  base := (23337918590126600139388244796202033877879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-224375057566830622456169329043250000000000000)
      constant := (4043671139493150306201171895104294144985143439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree010.table
  base := (5709418413013251608304948559251617702949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (875560)
      previous := (0)
      next := (500850)
      square := (3665279888136396039747914839540000000000000)
      linear := (-56587737422453800632876283047812500000000000)
      constant := (997500778050021610321225904232451912251603309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree010.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel010

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7216726308668013587/5000000000000000000)
  centralHi := (144334526173360271741/100000000000000000000)
  directionLo := (152141949236335141853/100000000000000000000)
  directionHi := (76070974618167570927/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree011.table
  base := (6024346753807591313209908063547146699/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 68820500000000000000000000000000000000000000
      center := (173257)
      previous := (0)
      next := (102025)
      square := (733055977627279207949582967908000000000000)
      linear := (-12141494499775330017990286522278500000000000)
      constant := (181593609065085513564925055611177601007529440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree011.table
  base := (9408959995523360375452146192446961691421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-122501685665394819221337556954185000000000000)
      constant := (1793319411780080044167392677186572254168877861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree011.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel011

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152141949236335141853/100000000000000000000)
  centralHi := (76070974618167570927/50000000000000000000)
  directionLo := (159567822536922327893/100000000000000000000)
  directionHi := (79783911268461163947/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree012.table
  base := (3964729905527131245095355891535526595457/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-65321180606045644565860532961972500000000000)
      constant := (829979705262009631664545670739876416125296937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree012.table
  base := (964928835109379931043874190150007910321/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-32956974121470509294230636953186250000000000)
      constant := (410415699011310192608714445120854477568985522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree012.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel012

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159567822536922327893/100000000000000000000)
  centralHi := (79783911268461163947/50000000000000000000)
  directionLo := (41665788769773319197/25000000000000000000)
  directionHi := (166663155079093276789/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree013.table
  base := (12973409084209524388622756439693073871679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-279739554852858556167078533250210000000000000)
      constant := (3093009209500258877433705036668859380771769239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree013.table
  base := (3147986879777891485942063422643966550287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (875560)
      previous := (0)
      next := (500850)
      square := (3665279888136396039747914839540000000000000)
      linear := (-70577053653184627566253769335652500000000000)
      constant := (766280613377978808210968318324548199948052967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree013.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel013

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41665788769773319197/25000000000000000000)
  centralHi := (166663155079093276789/100000000000000000000)
  directionLo := (173468511645949891193/100000000000000000000)
  directionHi := (86734255822974945597/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree014.table
  base := (1053247172499288651643932875353752795791/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19663000000000000000000000000000000000000000
      center := (49502)
      previous := (0)
      next := (29150)
      square := (209444565036365487985595133688000000000000)
      linear := (-4259919818307636201010213352179000000000000)
      constant := (41984374260976115356745400995613841223638433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree014.table
  base := (2037525157738838810827287629839391226043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39326000000000000000000000000000000000000000
      center := (100064)
      previous := (0)
      next := (57240)
      square := (418889130072730975971190267376000000000000)
      linear := (-8598875321534655605033858830278000000000000)
      constant := (83420093947493706321476864095627949677683509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree014.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel014

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173468511645949891193/100000000000000000000)
  centralHi := (86734255822974945597/50000000000000000000)
  directionLo := (45004195501922520031/25000000000000000000)
  directionHi := (1440134256061520641/800000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree015.table
  base := (8462527333828026022280433949462934494443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-316649219710210511974351336054850000000000000)
      constant := (2847482133580841722277220980652902766749628963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree015.table
  base := (2037983692275528679898311025554211319037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (875560)
      previous := (0)
      next := (500850)
      square := (3665279888136396039747914839540000000000000)
      linear := (-79903264473671845521838760194212500000000000)
      constant := (709221993698012255393545038219057200163571717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree015.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel015

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45004195501922520031/25000000000000000000)
  centralHi := (1440134256061520641/800000000000000000)
  directionLo := (186335072050720953051/100000000000000000000)
  directionHi := (46583768012680238263/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree016.table
  base := (1675653048160410171095306895016375867877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-83776013034721622469496934364292500000000000)
      constant := (702586477079618107060724703740888990830458157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree016.table
  base := (1284743989988782991062864008849481335017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (700448)
      previous := (0)
      next := (400680)
      square := (2932223910509116831798331871632000000000000)
      linear := (-67653095907132363599705004498794000000000000)
      constant := (561651829087287731833426887266563460433074897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree016.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel016

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186335072050720953051/100000000000000000000)
  centralHi := (46583768012680238263/25000000000000000000)
  directionLo := (96223017448906847827/50000000000000000000)
  directionHi := (38489206979562739131/20000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree017.table
  base := (5202157787411591768779641945482990681483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-353558884567562467781624138859490000000000000)
      constant := (2820537221642698995387938612348189320390001603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree017.table
  base := (619044532088630904139217400209512442017/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-44614737647079531738711875526386250000000000)
      constant := (353356089276842795212939243333742502031661897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree017.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel017

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96223017448906847827/50000000000000000000)
  centralHi := (38489206979562739131/20000000000000000000)
  directionLo := (4959220806968676703/2500000000000000000)
  directionHi := (198368832278747068121/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree018.table
  base := (1959584300956754112832320310977136755789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-186006858498119222842630270130905000000000000)
      constant := (1436137884352441384022649754201949080203553749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree018.table
  base := (3695883949534209976003871692949360167979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-375570322817610689820864985928210000000000000)
      constant := (2886881300572435436825164319360682882880797539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree018.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel018

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4959220806968676703/2500000000000000000)
  centralHi := (198368832278747068121/100000000000000000000)
  directionLo := (102059922216530278247/50000000000000000000)
  directionHi := (40823968886612111299/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree019.table
  base := (1409363115776100413978476975224837217797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-195234274712457211794448470832065000000000000)
      constant := (1480377672689068652905281873996089319494796877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree019.table
  base := (104779269183730322150442303891767667179/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (700448)
      previous := (0)
      next := (400680)
      square := (2932223910509116831798331871632000000000000)
      linear := (-78844548891717025146406993529066000000000000)
      constant := (596712813223557688532594155849985967390923695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree019.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel019

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102059922216530278247/50000000000000000000)
  centralHi := (40823968886612111299/20000000000000000000)
  directionLo := (8388528182046717123/4000000000000000000)
  directionHi := (52428301137791982019/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree020.table
  base := (1871760453728571481804729614269911679127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-408923381853590401492533343066450000000000000)
      constant := (3081974697153700147947868526390224913426719407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree020.table
  base := (13236055284776329074198604051525973189/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-51609395762444945205400618670306250000000000)
      constant := (389114304315454016810652655176597383611314384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree020.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel020

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8388528182046717123/4000000000000000000)
  centralHi := (52428301137791982019/25000000000000000000)
  directionLo := (5379030200397602719/2500000000000000000)
  directionHi := (215161208015904108761/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree021.table
  base := (105403880932778759204098894650159209889/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19663000000000000000000000000000000000000000
      center := (49502)
      previous := (0)
      next := (29150)
      square := (209444565036365487985595133688000000000000)
      linear := (-6105403061175233991373853492411000000000000)
      constant := (46179977773236380303226224755791580544047407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree021.table
  base := (896009357798544347053905377206258802099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (500320)
      previous := (0)
      next := (286200)
      square := (2094445650363654879855951336880000000000000)
      linear := (-61646798248647713936339275868510000000000000)
      constant := (467374107046312221444530125041886666825672637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree021.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel021

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5379030200397602719/2500000000000000000)
  centralHi := (215161208015904108761/100000000000000000000)
  directionLo := (220474630528336108677/100000000000000000000)
  directionHi := (110237315264168054339/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree022.table
  base := (345335146399969789567783276011323155593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-445833046710942357299806145871090000000000000)
      constant := (3409842638516143379402454614494264530458976113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree022.table
  base := (51201653893736111787767090794832644791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (875560)
      previous := (0)
      next := (500850)
      square := (3665279888136396039747914839540000000000000)
      linear := (-112545002345377108366386228199172500000000000)
      constant := (864229053278533690918893521446151560061678031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree022.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel022

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220474630528336108677/100000000000000000000)
  centralHi := (110237315264168054339/50000000000000000000)
  directionLo := (14103936171878672899/6250000000000000000)
  directionHi := (45132595750011753277/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree023.table
  base := (-27125517292764414740539163890575783443/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137641000000000000000000000000000000000000000
      center := (346514)
      previous := (0)
      next := (204050)
      square := (1466111955254558415899165935816000000000000)
      linear := (-46428787913961833520344254727341000000000000)
      constant := (361138050906104555750825837682428758591122037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree023.table
  base := (-396127456004625008177026032073019397511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-468832431022482869376714894513810000000000000)
      constant := (3666503499310899691000869433436677537107188449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree023.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel023

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14103936171878672899/6250000000000000000)
  centralHi := (45132595750011753277/20000000000000000000)
  directionLo := (14420918135929291269/6250000000000000000)
  directionHi := (46146938034973732061/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree024.table
  base := (-202469947974738368524352198206183083933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-120685677892073578276769737168932500000000000)
      constant := (958816189999379904538916530512292754144377947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree024.table
  base := (-920773635755667557698941241845476626909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-487484852663457305287884876230930000000000000)
      constant := (3898456279537535609507953078727306751595618331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree024.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel024

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14420918135929291269/6250000000000000000)
  centralHi := (46146938034973732061/20000000000000000000)
  directionLo := (117848647130372046337/50000000000000000000)
  directionHi := (9427891770429763707/4000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree025.table
  base := (-641197588300423574987060869971759156773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-250598771998485145505357675039025000000000000)
      constant := (2039931727738450039037419150557779597902607507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree025.table
  base := (-1380828665195998802971746558436058243747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-506137274304431741199054857948050000000000000)
      constant := (4151164602594788861982908447195302507272419173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree025.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel025

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117848647130372046337/50000000000000000000)
  centralHi := (9427891770429763707/4000000000000000000)
  directionLo := (15034846476391694973/6250000000000000000)
  directionHi := (240557543622267119569/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree026.table
  base := (-849375686917164510084378770122348342629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-259826188212823134457175875740185000000000000)
      constant := (2171903530553724983508896204130194851772201811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree026.table
  base := (-223261533450631238587469879949263652541/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-65598711993175772138778104958146250000000000)
      constant := (552909953096344407935583579336873401600604219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree026.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel026

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15034846476391694973/6250000000000000000)
  centralHi := (240557543622267119569/100000000000000000000)
  directionLo := (61330380453594380329/25000000000000000000)
  directionHi := (245321521814377521317/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree027.table
  base := (-2067310146097422777799066201437565537639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-538107208854322246817988152882690000000000000)
      constant := (4625944655537178805840108214672547041833830401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree027.table
  base := (-2144786527595483490369094298962886453887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-543442117586380613021394821382290000000000000)
      constant := (4713669650117263318955109202048889345600539433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree027.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel027

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61330380453594380329/25000000000000000000)
  centralHi := (245321521814377521317/100000000000000000000)
  directionLo := (124997366309319957591/50000000000000000000)
  directionHi := (249994732618639915183/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree028.table
  base := (-2395108304094060337247409632496456948347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (495020)
      previous := (0)
      next := (291500)
      square := (2094445650363654879855951336880000000000000)
      linear := (-79508863040428317817374936326430000000000000)
      constant := (703615383586283814559183292119842167024652939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree028.table
  base := (-2463819747664150296988881562635861256029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (500320)
      previous := (0)
      next := (286200)
      square := (2094445650363654879855951336880000000000000)
      linear := (-80299219889622149847509257585630000000000000)
      constant := (717340544710049142064266370492611060122701773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree028.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel028

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124997366309319957591/50000000000000000000)
  centralHi := (249994732618639915183/100000000000000000000)
  directionLo := (31822771821254533709/12500000000000000000)
  directionHi := (254582174570036269673/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree029.table
  base := (-672018980253393691612284090318873836627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-143754218427918550656315238921832500000000000)
      constant := (1310269982151005165609156898009266136252823093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree029.table
  base := (-549800937359673820854820607539198889139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (700448)
      previous := (0)
      next := (400680)
      square := (2932223910509116831798331871632000000000000)
      linear := (-116149392173665896968746956963306000000000000)
      constant := (1069124407874044749272149788585609125700018901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree029.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel029

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31822771821254533709/12500000000000000000)
  centralHi := (254582174570036269673/100000000000000000000)
  directionLo := (259088403601071230643/100000000000000000000)
  directionHi := (64772100900267807661/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree030.table
  base := (-1475608683950159794098691200478554525129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-296735853070175090264448678544825000000000000)
      constant := (2786286289701182412088185911138306276606719311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree030.table
  base := (-3005239283954360610432453029014916646631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-599399382509303920754904766533650000000000000)
      constant := (5685710172101029401565756998671357857841062529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree030.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel030

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259088403601071230643/100000000000000000000)
  centralHi := (64772100900267807661/25000000000000000000)
  directionLo := (131758793019948708241/50000000000000000000)
  directionHi := (263517586039897416483/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree031.table
  base := (-797190420854585416792887746982273115649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-152981634642256539608133439622992500000000000)
      constant := (1479800887097065278158044498674471696088955991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree031.table
  base := (-647331299934981439363125837006142661757/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (700448)
      previous := (0)
      next := (400680)
      square := (2932223910509116831798331871632000000000000)
      linear := (-123610360830055671333214949650154000000000000)
      constant := (1208215869268138370062651948929909517893104763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree031.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel031

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131758793019948708241/50000000000000000000)
  centralHi := (263517586039897416483/100000000000000000000)
  directionLo := (133936771858998729271/50000000000000000000)
  directionHi := (267873543717997458543/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree032.table
  base := (-680857525067259418883895555214270214491/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (2932223910509116831798331871632000000000000)
      linear := (-126076274199540427267234031978858000000000000)
      constant := (1256096050352734786955226192413040633407244269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree032.table
  base := (-3446748710218519940769246814001057125401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-636704225791252792577244729967890000000000000)
      constant := (6411248867928613369406329344218720496202680959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree032.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel032

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133936771858998729271/50000000000000000000)
  centralHi := (267873543717997458543/100000000000000000000)
  directionLo := (10886391703096563013/4000000000000000000)
  directionHi := (136079896288707037663/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree033.table
  base := (-3600827797181736569966541061045399288117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-648836203426378114239806561296610000000000000)
      constant := (6655985278946467684706037630385415196584288003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree033.table
  base := (-3638471109933899995833938455586377818519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-655356647432227228488414711685010000000000000)
      constant := (6795811980959444383370479593987475370681226321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree033.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel033

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10886391703096563013/4000000000000000000)
  centralHi := (136079896288707037663/50000000000000000000)
  directionLo := (276379575887083616343/100000000000000000000)
  directionHi := (34547446985885452043/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree034.table
  base := (-756191092542251941838916061822187547059/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (2932223910509116831798331871632000000000000)
      linear := (-133458207171010818428688592539786000000000000)
      constant := (1409072888667984046952225246736614283835252181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree034.table
  base := (-3814327778289011060768477553480511169039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-674009069073201664399584693402130000000000000)
      constant := (7194424021431134900744854158392348962182303001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree034.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel034

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276379575887083616343/100000000000000000000)
  centralHi := (34547446985885452043/12500000000000000000)
  directionLo := (280535892960717897263/100000000000000000000)
  directionHi := (17533493310044868579/6250000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree035.table
  base := (-3946857021323481715996160208854161908411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (495020)
      previous := (0)
      next := (291500)
      square := (2094445650363654879855951336880000000000000)
      linear := (-97963695469104295721011337728750000000000000)
      constant := (1064045258106343827094631467950925614394914507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree035.table
  base := (-99411085367111268411467989287747998833/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4915750000000000000000000000000000000000000
      center := (12508)
      previous := (0)
      next := (7155)
      square := (52361141259091371996398783422000000000000)
      linear := (-2473791038264914643966980982568750000000000)
      constant := (27167116227119597382664010734060011098946721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree035.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel035

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280535892960717897263/100000000000000000000)
  centralHi := (17533493310044868579/6250000000000000000)
  directionLo := (284631524099159697041/100000000000000000000)
  directionHi := (142315762049579848521/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree036.table
  base := (-4100392593404589398349563869720769338611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-704200700712406047950715765503570000000000000)
      constant := (7864586340329852210972980890838423587464243349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree036.table
  base := (-4126623209903937803476795140601275406297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-711313912355150536221924656836370000000000000)
      constant := (8032669079181839645896957503249459851801874623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree036.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel036

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284631524099159697041/100000000000000000000)
  centralHi := (142315762049579848521/50000000000000000000)
  directionLo := (288669052346720543481/100000000000000000000)
  directionHi := (144334526173360271741/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree037.table
  base := (-1060786683683235290466488165281029121683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-180663883285270506463588041726472500000000000)
      constant := (2073488736063591867346520554295370120662430197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree037.table
  base := (-853280577158617837035049021383107798731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (700448)
      previous := (0)
      next := (400680)
      square := (2932223910509116831798331871632000000000000)
      linear := (-145993266799224994426618927710698000000000000)
      constant := (1694368449981127895610158115384775659474866429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree037.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel037

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288669052346720543481/100000000000000000000)
  centralHi := (144334526173360271741/50000000000000000000)
  directionLo := (292650882545221180881/100000000000000000000)
  directionHi := (146325441272610590441/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree038.table
  base := (-2188235473135514597698599463288159329189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-370555182784879001878994284154105000000000000)
      constant := (4368118298286987088767981846726149461771096851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree038.table
  base := (-4397090576627366990370994267868978844191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-748618755637099408044264620270610000000000000)
      constant := (8924132002855077883487751880518885882906706569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree038.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel038

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292650882545221180881/100000000000000000000)
  centralHi := (146325441272610590441/50000000000000000000)
  directionLo := (296579258084984765109/100000000000000000000)
  directionHi := (29657925808498476511/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree039.table
  base := (-1125379838976492537611960436423656643969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-189891299499608495415406242427632500000000000)
      constant := (2297818110493040428098222264048320225867462871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree039.table
  base := (-141243810377489563138402541128843789787/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-95908897159759230494429325248466250000000000)
      constant := (1173673097361690993606647956442234247719710132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree039.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel039

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296579258084984765109/100000000000000000000)
  centralHi := (29657925808498476511/10000000000000000000)
  directionLo := (300456275684138704741/100000000000000000000)
  directionHi := (150228137842069352371/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree040.table
  base := (-4619278710513901266318311647979572592431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-778020030427109959565261371112850000000000000)
      constant := (9658926663622151668202307746893443648805204729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree040.table
  base := (-4635489580882814444004179068205673880949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-785923598919048279866604583704850000000000000)
      constant := (9867469457249574472185205484241102841352298691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree040.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel040

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300456275684138704741/100000000000000000000)
  centralHi := (150228137842069352371/50000000000000000000)
  directionLo := (152141949236335141853/50000000000000000000)
  directionHi := (304283898472670283707/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree041.table
  base := (-4730593620774464580114546887861651169597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-796474862855785937468897772515170000000000000)
      constant := (10139083008465387435334921318274719471365499323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree041.table
  base := (-118624197413920800733172911135379010439/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34410250000000000000000000000000000000000000
      center := (87556)
      previous := (0)
      next := (50085)
      square := (366527988813639603974791483954000000000000)
      linear := (-20114400514000567894444364135549250000000000)
      constant := (258956848668438710314121699196804297624165601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree041.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel041

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152141949236335141853/50000000000000000000)
  centralHi := (304283898472670283707/100000000000000000000)
  directionLo := (61612793522601935319/20000000000000000000)
  directionHi := (77015991903252419149/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree042.table
  base := (-1209046959954710518508758981188176293051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49157500000000000000000000000000000000000000
      center := (123755)
      previous := (0)
      next := (72875)
      square := (523611412590913719963987834220000000000000)
      linear := (-29104631974445068406161934782767500000000000)
      constant := (379701494942754999806390986439114389549738187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree042.table
  base := (-1212233461019262337740254880263149989069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49157500000000000000000000000000000000000000
      center := (125080)
      previous := (0)
      next := (71550)
      square := (523611412590913719963987834220000000000000)
      linear := (-29401015792892755417462305254967500000000000)
      constant := (387917939871474296227807776920565681764936253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree042.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel042

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61612793522601935319/20000000000000000000)
  centralHi := (77015991903252419149/25000000000000000000)
  directionLo := (155899106326185071611/50000000000000000000)
  directionHi := (311798212652370143223/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree043.table
  base := (-4936682223825633558004378505004918384113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-833384527713137893276170575319810000000000000)
      constant := (11136517758152130689496554819267233028692302567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree043.table
  base := (-2473992276346070254207704647987857572301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-420940431920985793800057264428105000000000000)
      constant := (5688836188386926682947973723236523295890918059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree043.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel043

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155899106326185071611/50000000000000000000)
  centralHi := (311798212652370143223/100000000000000000000)
  directionLo := (157744130386011344917/50000000000000000000)
  directionHi := (63097652154404537967/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree044.table
  base := (-251630495649460064799837142044179947983/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 68820500000000000000000000000000000000000000
      center := (173257)
      previous := (0)
      next := (102025)
      square := (733055977627279207949582967908000000000000)
      linear := (-42591968007090693558990348836106500000000000)
      constant := (582681866289043365185603721414320027779671897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree044.table
  base := (-2521316075018744237921516608957656963411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-430266642741473011755642255286665000000000000)
      constant := (5953056819047702939585735603155339137899146549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree044.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel044

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157744130386011344917/50000000000000000000)
  centralHi := (63097652154404537967/20000000000000000000)
  directionLo := (319135645073844655787/100000000000000000000)
  directionHi := (79783911268461163947/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree045.table
  base := (-5124429180709536720431813848269627827827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-870294192570489849083443378124450000000000000)
      constant := (12182937484074301616475828595845945156150063893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree045.table
  base := (-128332907549180036319070232081647828863/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34410250000000000000000000000000000000000000
      center := (87556)
      previous := (0)
      next := (50085)
      square := (366527988813639603974791483954000000000000)
      linear := (-21979642678098011485561362307261250000000000)
      constant := (311174139607952813187880141033674911187467817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree045.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel045

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319135645073844655787/100000000000000000000)
  centralHi := (79783911268461163947/25000000000000000000)
  directionLo := (322741812023856163141/100000000000000000000)
  directionHi := (161370906011928081571/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree046.table
  base := (-5212534323983320984473066263294757565829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-888749024999165826987079779526770000000000000)
      constant := (12724363961599513437185243495789956273881730611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree046.table
  base := (-5220414827668081762299982539792953145821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-897838128764894895333624474007570000000000000)
      constant := (13000176212031282652369868897962518136056051739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree046.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel046

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322741812023856163141/100000000000000000000)
  centralHi := (161370906011928081571/50000000000000000000)
  directionLo := (326308128155253381461/100000000000000000000)
  directionHi := (163154064077626690731/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree047.table
  base := (-1324316226505715652808742412496556045663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-226800964356960451222679045232272500000000000)
      constant := (3319467505134099352102580105714040279318899017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree047.table
  base := (-5304252697778524296567300347666851256277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-916490550405869331244794455724690000000000000)
      constant := (13565700791951276942390170316756026926234777443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree047.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel047

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326308128155253381461/100000000000000000000)
  centralHi := (163154064077626690731/50000000000000000000)
  directionLo := (164917943059517043027/50000000000000000000)
  directionHi := (65967177223806817211/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree048.table
  base := (-1075782722161564329488107228525884606503/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (2932223910509116831798331871632000000000000)
      linear := (-185131737971303556558870516466282000000000000)
      constant := (2768683075113861828332011452773876716876320577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree048.table
  base := (-1346277418022803998475449787135041401621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (875560)
      previous := (0)
      next := (500850)
      square := (3665279888136396039747914839540000000000000)
      linear := (-233785743011710941788991109360452500000000000)
      constant := (3535875204415117543674115466215505766439483939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree048.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel048

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (164917943059517043027/50000000000000000000)
  centralHi := (65967177223806817211/20000000000000000000)
  directionLo := (41665788769773319197/12500000000000000000)
  directionHi := (333326310158186553577/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree049.table
  base := (-2728866463355507070384169174847500102971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (247510)
      previous := (0)
      next := (145750)
      square := (1047222825181827439927975668440000000000000)
      linear := (-67436680163228125764142070266695000000000000)
      constant := (1030068948139008990236851971887651105475281227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree049.table
  base := (-1092645358214006859595173241544579715971/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39326000000000000000000000000000000000000000
      center := (100064)
      previous := (0)
      next := (57240)
      square := (418889130072730975971190267376000000000000)
      linear := (-27251296962509091516203840547398000000000000)
      constant := (420958374631667822687549499619884929044862227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree049.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel049

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41665788769773319197/12500000000000000000)
  centralHi := (333326310158186553577/100000000000000000000)
  directionLo := (67356112214234793479/20000000000000000000)
  directionHi := (84195140267793491849/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree050.table
  base := (-2766970420498912800580679180554224792689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-481284177356934869300812692568025000000000000)
      constant := (7505244855840826323201934726344960945309493351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree050.table
  base := (-2769405950151455964602206598642925539323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-486223907664396319489152200438025000000000000)
      constant := (7667899533610209576461426662401189085842042957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree050.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel050

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67356112214234793479/20000000000000000000)
  centralHi := (84195140267793491849/25000000000000000000)
  directionLo := (340199740721767594157/100000000000000000000)
  directionHi := (170099870360883797079/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree051.table
  base := (-5607725697617836539476643455017511636647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-981023187142545716505261786538370000000000000)
      constant := (15611962764926325279829007958246269680820270273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree051.table
  base := (-1403011089467284229747662138336081071797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (875560)
      previous := (0)
      next := (500850)
      square := (3665279888136396039747914839540000000000000)
      linear := (-247775059242441768722368595648292500000000000)
      constant := (3987560998992803741835488841706473465196789123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree051.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel051

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340199740721767594157/100000000000000000000)
  centralHi := (170099870360883797079/50000000000000000000)
  directionLo := (343584896144899032713/100000000000000000000)
  directionHi := (171792448072449516357/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree052.table
  base := (-5679250346251345769441537037690350016757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-999478019571221694408898187940690000000000000)
      constant := (16225362018887297754571097849314002533343549763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree052.table
  base := (-1136615810075333976112276009260904851537/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (700448)
      previous := (0)
      next := (400680)
      square := (2932223910509116831798331871632000000000000)
      linear := (-201950531722148302160128872862058000000000000)
      constant := (3315371315922630986111277512888007795329595783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree052.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel052

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (343584896144899032713/100000000000000000000)
  centralHi := (171792448072449516357/50000000000000000000)
  directionLo := (346937023291899782387/100000000000000000000)
  directionHi := (86734255822974945597/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree053.table
  base := (-5748655690191026264726735872625839921041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25970000000000000000000000000000000000000000
      center := (65380)
      previous := (0)
      next := (38500)
      square := (276624897217841210547012440720000000000000)
      linear := (-19206280226413163628538388478170000000000000)
      constant := (317937133575367231506813787786195693725056523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree053.table
  base := (-2876024911632587894449675154003254835433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12985000000000000000000000000000000000000000
      center := (33040)
      previous := (0)
      next := (18900)
      square := (138312448608920605273506220360000000000000)
      linear := (-9701934719355810818035984396485000000000000)
      constant := (162411494297415831280608964519393547192380499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree053.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel053

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346937023291899782387/100000000000000000000)
  centralHi := (86734255822974945597/25000000000000000000)
  directionLo := (437821338066374131/125000000000000000)
  directionHi := (350257070453099304801/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree054.table
  base := (-363503982726833612953314601819344029937/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-259096921107143412554042747686332500000000000)
      constant := (4371966038836294367213936676718812173501765532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree054.table
  base := (-5819072414169418367938872274271736750349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1047057501892690382622984327744530000000000000)
      constant := (17866513513466198009180400623873523881945213291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree054.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel054

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437821338066374131/125000000000000000)
  centralHi := (350257070453099304801/100000000000000000000)
  directionLo := (88386485347779034753/25000000000000000000)
  directionHi := (353545941391116139013/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree055.table
  base := (-1470395033677146916324248711664993502433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-263710629214312407029951848036912500000000000)
      constant := (4534233924854461259210522773037687379331619447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree055.table
  base := (-183882717628643896082224478533084121493/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-133213740441708102316769288682706250000000000)
      constant := (2316191018740298600542264182041286073734327948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree055.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel055

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88386485347779034753/25000000000000000000)
  centralHi := (353545941391116139013/100000000000000000000)
  directionLo := (356804498214181271121/100000000000000000000)
  directionHi := (178402249107090635561/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree056.table
  base := (-5945296538797112552408037117140059436543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (495020)
      previous := (0)
      next := (291500)
      square := (2094445650363654879855951336880000000000000)
      linear := (-153328192755132229431920541935710000000000000)
      constant := (2685410014525936105747215503104755011299254991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree056.table
  base := (-1189532033922781283604913906438724015047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39326000000000000000000000000000000000000000
      center := (100064)
      previous := (0)
      next := (57240)
      square := (418889130072730975971190267376000000000000)
      linear := (-30981781290703978698437836890822000000000000)
      constant := (548704296340020196571787816807391369692130839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree056.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel056

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356804498214181271121/100000000000000000000)
  centralHi := (178402249107090635561/50000000000000000000)
  directionLo := (45004195501922520031/12500000000000000000)
  directionHi := (360033564015380160249/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree057.table
  base := (-6007292396489593373180375292220514305449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1091752181714601583927080194952290000000000000)
      constant := (19470656425100588104631746669224041190483694191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree057.table
  base := (-300469356443821306604080107029869472449/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 68820500000000000000000000000000000000000000
      center := (175112)
      previous := (0)
      next := (100170)
      square := (733055977627279207949582967908000000000000)
      linear := (-55150738340780684517824713644794500000000000)
      constant := (994593492140386365416331937794583735942647191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree057.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel057

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45004195501922520031/12500000000000000000)
  centralHi := (360033564015380160249/100000000000000000000)
  directionLo := (363233925300707562837/100000000000000000000)
  directionHi := (181616962650353781419/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree058.table
  base := (-1516909165616993362773902651304266362161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-277551753535819390457679149088652500000000000)
      constant := (5038821294670893442264618614817051973645797799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree058.table
  base := (-1481809796686490621335393865153693269/2441406250000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-140208398557073515783458031826626250000000000)
      constant := (2573897200529301306775651794311996818437924352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree058.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel058

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363233925300707562837/100000000000000000000)
  centralHi := (181616962650353781419/50000000000000000000)
  directionLo := (366406334226229172689/100000000000000000000)
  directionHi := (36640633422622917269/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree059.table
  base := (-765798650541742996301838363805967408293/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-282165461642988384933588249439232500000000000)
      constant := (5212937030548486339304457141498399429910286374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree059.table
  base := (-6128033999809106613233291544003159997943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1140319610097562562178834236330130000000000000)
      constant := (21302565888391530200792777425599821054723127537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree059.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel059

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366406334226229172689/100000000000000000000)
  centralHi := (36640633422622917269/10000000000000000000)
  directionLo := (18477575533118943091/5000000000000000000)
  directionHi := (369551510662378861821/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree060.table
  base := (-6183602024612780653944094192437951627503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1147116679000629517637989399159250000000000000)
      constant := (21560038097952121393347009159900147900038859577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree060.table
  base := (-6185059303933209780714809973788785622073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1158972031738536998090004218047250000000000000)
      constant := (22026027956745559579013202905401737758192250207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree060.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel060

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18477575533118943091/5000000000000000000)
  centralHi := (369551510662378861821/100000000000000000000)
  directionLo := (186335072050720953051/50000000000000000000)
  directionHi := (372670144101441906103/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree061.table
  base := (-3119660157073885811627465966643870723187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-582785755714652747770812900280785000000000000)
      constant := (11140074442922620428552420139356063489789818133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree061.table
  base := (-3120305664273225870868249459879932951277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-588812226689755717000587099882185000000000000)
      constant := (11380778980537722061945842881777646148653282443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree061.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel061

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186335072050720953051/50000000000000000000)
  centralHi := (372670144101441906103/100000000000000000000)
  directionLo := (375762895422542529467/100000000000000000000)
  directionHi := (93940723855635632367/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree062.table
  base := (-786697920112774722880435265771352163529/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-296006585964495368361315550490972500000000000)
      constant := (5753018769559687450372005931356778133719409822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree062.table
  base := (-3147363482071386773366585406833377168211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-598138437510242934956172090740745000000000000)
      constant := (11754575411868353647652663991070967133190269749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree062.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel062

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (375762895422542529467/100000000000000000000)
  centralHi := (93940723855635632367/25000000000000000000)
  directionLo := (189415199263467101109/50000000000000000000)
  directionHi := (378830398526934202219/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree063.table
  base := (-3173212667317637277388856261430355727193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (247510)
      previous := (0)
      next := (145750)
      square := (1047222825181827439927975668440000000000000)
      linear := (-85891512591904103667778471669015000000000000)
      constant := (1696843712283772861190734782194517415336204041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree063.table
  base := (-1586859563252004238128885959978545640189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49157500000000000000000000000000000000000000
      center := (125080)
      previous := (0)
      next := (71550)
      square := (523611412590913719963987834220000000000000)
      linear := (-43390332023623582350839791542807500000000000)
      constant := (866742933371324412428748053555071857076963693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree063.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel063

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189415199263467101109/50000000000000000000)
  centralHi := (378830398526934202219/100000000000000000000)
  directionLo := (95468315463763601127/25000000000000000000)
  directionHi := (381873261855054404509/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree064.table
  base := (-1599468991228605376430941373916382766103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-305234002178833357313133751192132500000000000)
      constant := (6127838868760015606498387713083415159690816977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree064.table
  base := (-6398773036736467690132216420528261271941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1233581718302434741734684144915730000000000000)
      constant := (25040508060911693799683278180349429590268768819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree064.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel064

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95468315463763601127/25000000000000000000)
  centralHi := (381873261855054404509/100000000000000000000)
  directionLo := (96223017448906847827/25000000000000000000)
  directionHi := (384892069795627391309/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree065.table
  base := (-3223980563690549628318771638420843562581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-619695420572004703578085703085425000000000000)
      constant := (12639351012945655314078176145554179171202788579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree065.table
  base := (-6448755515478933535669698051250097151733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1252234139943409177645854126632850000000000000)
      constant := (25824265272347580717232002771060885377938318147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree065.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel065

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96223017448906847827/25000000000000000000)
  centralHi := (384892069795627391309/100000000000000000000)
  directionLo := (387887383996057888217/100000000000000000000)
  directionHi := (193943691998028944109/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree066.table
  base := (-3248351675514111118921016010291958282541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-628922836786342692529903903786585000000000000)
      constant := (13028924261806725464027302564898909570032774219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree066.table
  base := (-6497406731276784244977350653656156078281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1270886561584383613557024108349970000000000000)
      constant := (26620070872457128126086257247428673021229324879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree066.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel066

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387887383996057888217/100000000000000000000)
  centralHi := (193943691998028944109/50000000000000000000)
  directionLo := (195429872291218841107/50000000000000000000)
  directionHi := (78171948916487536443/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree067.table
  base := (-3272061128706436922357434599202675518581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-638150253000680681481722104487745000000000000)
      constant := (13424396133737872405032567984592752038946992579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree067.table
  base := (-409046561628123670815453034994872084349/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-161192372903169756183524261258386250000000000)
      constant := (3428490292768221370153452188287296622876238582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree067.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel067

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195429872291218841107/50000000000000000000)
  centralHi := (78171948916487536443/20000000000000000000)
  directionLo := (24613104456041899577/6250000000000000000)
  directionHi := (393809671296670393233/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree068.table
  base := (-3295117470583888868484864494312473339053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-647377669215018670433540305188905000000000000)
      constant := (13825765452277924778470647490846706857139406027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree068.table
  base := (-6590786203288934393506713915492567569621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1308191404866332485379364071784210000000000000)
      constant := (28247817489688364682179825300247127507149795939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree068.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel068

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24613104456041899577/6250000000000000000)
  centralHi := (393809671296670393233/100000000000000000000)
  directionLo := (4959220806968676703/1250000000000000000)
  directionHi := (396737664557494136241/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree069.table
  base := (-6635056299846082959628911740819945533069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1313210170858713318770717011780130000000000000)
      constant := (28466062384339652180977167724905386876882849771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree069.table
  base := (-6635544241208212306554425018833426273909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1326843826507306921290534053501330000000000000)
      constant := (29079754407626398887303254349597508374232891331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree069.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel069

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4959220806968676703/1250000000000000000)
  centralHi := (396737664557494136241/100000000000000000000)
  directionLo := (99911051612883990067/25000000000000000000)
  directionHi := (399644206451535960269/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree070.table
  base := (-6678599320000772396900580328691653397287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (495020)
      previous := (0)
      next := (291500)
      square := (2094445650363654879855951336880000000000000)
      linear := (-190237857612484185239193344740350000000000000)
      constant := (4184626417049287652143922636103186019249145719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree070.table
  base := (-3339515582009643056370574142759877850857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (250160)
      previous := (0)
      next := (143100)
      square := (1047222825181827439927975668440000000000000)
      linear := (-96106874867734382657264573944175000000000000)
      constant := (2137409388244981580945632615295912521818598809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree070.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel070

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99911051612883990067/25000000000000000000)
  centralHi := (399644206451535960269/100000000000000000000)
  directionLo := (201264880829978044367/50000000000000000000)
  directionHi := (80505952331991217747/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree071.table
  base := (-3360437662716209669463105431537758744973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-675059917858032637288994907292385000000000000)
      constant := (15065248475476349500401902125886328848583171307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree071.table
  base := (-1344251495408138350330887861888421143809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (700448)
      previous := (0)
      next := (400680)
      square := (2932223910509116831798331871632000000000000)
      linear := (-272829733957851158622574803387114000000000000)
      constant := (6155949425427169162945172270876847825344985431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree071.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel071

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201264880829978044367/50000000000000000000)
  centralHi := (80505952331991217747/20000000000000000000)
  directionLo := (81078955665145123451/20000000000000000000)
  directionHi := (50674347290715702157/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree072.table
  base := (-1690473548177974256939444450337232235651/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-342143667036185313120406553996772500000000000)
      constant := (7745099279935404231114232326442143017852760709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree072.table
  base := (-3381116165280951205605775898794803351067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-691400545715115114512021999326345000000000000)
      constant := (15823900111644858276353074926419104471955787053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree072.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel072

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81078955665145123451/20000000000000000000)
  centralHi := (50674347290715702157/12500000000000000000)
  directionLo := (102059922216530278247/25000000000000000000)
  directionHi := (408239688866121112989/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree073.table
  base := (-6801664538376784764489265406221175956777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1387029500573417230385262617389410000000000000)
      constant := (31842084239722918383384956526806476120133256943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree073.table
  base := (-850245462086444399942413510504182252531/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-175181689133900583116901747546226250000000000)
      constant := (4065986203325293678372504769577598850579380629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree073.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel073

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102059922216530278247/25000000000000000000)
  centralHi := (408239688866121112989/100000000000000000000)
  directionLo := (411064910734607130549/100000000000000000000)
  directionHi := (8221298214692142611/2000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree074.table
  base := (-53439014699951095801967888345459215333/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-351371083250523302072224754697932500000000000)
      constant := (8178889318987746360809933952307167240555217504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree074.table
  base := (-6840458522833674054838938574053166072087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1420105934712179100846383962086930000000000000)
      constant := (33420014380826107178669570711518908168671873233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree074.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel074

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411064910734607130549/100000000000000000000)
  centralHi := (8221298214692142611/2000000000000000000)
  directionLo := (103467711783976866899/25000000000000000000)
  directionHi := (413870847135907467597/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree075.table
  base := (-687748878555893966149668056106443333781/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137641000000000000000000000000000000000000000
      center := (346514)
      previous := (0)
      next := (204050)
      square := (1466111955254558415899165935816000000000000)
      linear := (-142393916543076918619253542019405000000000000)
      constant := (3360081532506093322403861615293890533095049379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree075.table
  base := (-3438861432466265905265174294701747000757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-719379178176576768378776971902025000000000000)
      constant := (17162086826207382075354999164570456841068805763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree075.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel075

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103467711783976866899/25000000000000000000)
  centralHi := (413870847135907467597/100000000000000000000)
  directionLo := (41665788769773319197/10000000000000000000)
  directionHi := (416657887697733191971/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree076.table
  base := (-432097186278879912964099510510158920677/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-360598499464861291024042955399092500000000000)
      constant := (8624464399585930456828796544856599863996388172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree076.table
  base := (-432110125199707101344919607372485580193/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-182176347249265996583590490690146250000000000)
      constant := (4405045839324415396399377217049507424513310574) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree076.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel076

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41665788769773319197/10000000000000000000)
  centralHi := (416657887697733191971/100000000000000000000)
  directionLo := (8388528182046717123/2000000000000000000)
  directionHi := (419426409102335856151/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree077.table
  base := (-6948397470455594321335840457668780192069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (495020)
      previous := (0)
      next := (291500)
      square := (2094445650363654879855951336880000000000000)
      linear := (-208692690041160163142829746142670000000000000)
      constant := (5058097629574686520221133170160553775083347253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree077.table
  base := (-3474290271315624274294026471504994531557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (250160)
      previous := (0)
      next := (143100)
      square := (1047222825181827439927975668440000000000000)
      linear := (-105433085688221600612849564802735000000000000)
      constant := (2583470923823550638783518269743257292525994709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree077.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel077

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8388528182046717123/2000000000000000000)
  centralHi := (419426409102335856151/100000000000000000000)
  directionLo := (105544193920196043703/25000000000000000000)
  directionHi := (422176775680784174813/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree078.table
  base := (-1745505156685142424979608481960761654931/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-369825915679199279975861156100252500000000000)
      constant := (9081823037360424103938351771830586305053642229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree078.table
  base := (-3491091250213722456027485783738594519093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-747357810638038422245531944477705000000000000)
      constant := (18554425878144135344858007289334956111797520387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree078.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel078

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105544193920196043703/25000000000000000000)
  centralHi := (422176775680784174813/100000000000000000000)
  directionLo := (424909339972618533373/100000000000000000000)
  directionHi := (212454669986309266687/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree079.table
  base := (-1402885653719292124552890084175523350483/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (2932223910509116831798331871632000000000000)
      linear := (-299551699029094619561416205160666000000000000)
      constant := (7451936659982190112641763064548923790516169397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree079.table
  base := (-7014571381907733769065932646629928300489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1513368042917051280402233870672530000000000000)
      constant := (38061142700394730980898597821798770038792393551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree079.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel079

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424909339972618533373/100000000000000000000)
  centralHi := (212454669986309266687/50000000000000000000)
  directionLo := (5345305540666464619/1250000000000000000)
  directionHi := (427624443253317169521/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree080.table
  base := (-1409124746787351401312039992358919339509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (2932223910509116831798331871632000000000000)
      linear := (-303242665514829815142143485441130000000000000)
      constant := (7640771279799363483658307299847325983190641731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree080.table
  base := (-3522875123292485543208110474719387931751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-766010232279012858156701926194825000000000000)
      constant := (19512732672367340404195667857453148725685860609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree080.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel080

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5345305540666464619/1250000000000000000)
  centralHi := (427624443253317169521/100000000000000000000)
  directionLo := (430322416031808217521/100000000000000000000)
  directionHi := (215161208015904108761/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree081.table
  base := (-884451242595167541407757669698315402463/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-383667040000706263403588457151992500000000000)
      constant := (9789952761265718823554723670356279589379180434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree081.table
  base := (-110558152587718948982002755599184156707/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-193834110774875019028071729263346250000000000)
      constant := (5000227415205961831911172731779126547893534504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree081.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel081

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430322416031808217521/100000000000000000000)
  centralHi := (215161208015904108761/50000000000000000000)
  directionLo := (216501789260040407611/50000000000000000000)
  directionHi := (433003578520080815223/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree082.table
  base := (-7104389440693859424493595903934926220949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1553122992431501031517990230010290000000000000)
      constant := (40127546886901093542707955269011182820022358691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree082.table
  base := (-7104488271777309355567384056225536272977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1569325307839974588135743815823890000000000000)
      constant := (40990204310047263232886558289623700961851172743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree082.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel082

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216501789260040407611/50000000000000000000)
  centralHi := (433003578520080815223/100000000000000000000)
  directionLo := (108917060269196048327/25000000000000000000)
  directionHi := (435668241076784193309/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree083.table
  base := (-7131964465634838687576611488973816847709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1571577824860177009421626631412610000000000000)
      constant := (41107063617310452084636383302464169875264485531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree083.table
  base := (-7132051802983808897121688447038121492889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1587977729480949024046913797541010000000000000)
      constant := (41990620029433561036596791169472065919597265151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree083.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel083

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108917060269196048327/25000000000000000000)
  centralHi := (435668241076784193309/100000000000000000000)
  directionLo := (438316704626554368561/100000000000000000000)
  directionHi := (219158352313277184281/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree084.table
  base := (-7158336968424980005357927741671446181163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (495020)
      previous := (0)
      next := (291500)
      square := (2094445650363654879855951336880000000000000)
      linear := (-227147522469836141046466147544990000000000000)
      constant := (6014051566785714838838853954461894353739791931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree084.table
  base := (-7158414140131222585429986695014191760763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (500320)
      previous := (0)
      next := (286200)
      square := (2094445650363654879855951336880000000000000)
      linear := (-229518593017417637136869111322590000000000000)
      constant := (6143295176383149456510482509885215947408117131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree084.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel084

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438316704626554368561/100000000000000000000)
  centralHi := (219158352313277184281/50000000000000000000)
  directionLo := (88189852211334443471/20000000000000000000)
  directionHi := (110237315264168054339/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree085.table
  base := (-7183508658295247112882999205081772773921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1608487489717528965228899434217250000000000000)
      constant := (43101438702209489824959346996557964713624739639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree085.table
  base := (-143671536801376340319187291258915611151/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137641000000000000000000000000000000000000000
      center := (350224)
      previous := (0)
      next := (200340)
      square := (1466111955254558415899165935816000000000000)
      linear := (-162528257276289789586925376097525000000000000)
      constant := (4402754271150642880634963233732057981827826045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree085.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel085

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88189852211334443471/20000000000000000000)
  centralHi := (110237315264168054339/25000000000000000000)
  directionLo := (443566193592532955167/100000000000000000000)
  directionHi := (13861443549766654849/3125000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree086.table
  base := (-3603740515889141705892793516121290786489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-813471161073102471566267917809785000000000000)
      constant := (22058148307727330186727109364786504414856867551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree086.table
  base := (-3603770632150135259589553741563178127993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-821967497201936165890211871346185000000000000)
      constant := (22532024636253990539920716278828982599284915487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree086.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel086

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443566193592532955167/100000000000000000000)
  centralHi := (13861443549766654849/3125000000000000000)
  directionLo := (89233555430658837237/20000000000000000000)
  directionHi := (223083888576647093093/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree087.table
  base := (-56486370309901012763494796531041457603/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-411349288643720230259043059255472500000000000)
      constant := (11285733631704155767452488178222598277490095264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree087.table
  base := (-1446061720796332116280402845237608775929/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (700448)
      previous := (0)
      next := (400680)
      square := (2932223910509116831798331871632000000000000)
      linear := (-332517483208969353538318744881898000000000000)
      constant := (9222517150746957870951039658924018290472356511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree087.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel087

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89233555430658837237/20000000000000000000)
  centralHi := (223083888576647093093/50000000000000000000)
  directionLo := (17950171147558665637/4000000000000000000)
  directionHi := (224377139344483320463/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree088.table
  base := (-7251832910532204982869545306158647084761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1663851987003556898939808638424210000000000000)
      constant := (46181352278205079428946582719599457656606411199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree088.table
  base := (-906484987712064705453544557134015399007/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-210154979710727650450345463265826250000000000)
      constant := (5896644001460576739707651394496596986465277513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree088.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel088

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17950171147558665637/4000000000000000000)
  centralHi := (224377139344483320463/50000000000000000000)
  directionLo := (14103936171878672899/3125000000000000000)
  directionHi := (451325957500117532769/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree089.table
  base := (-7272214571235487496615140902408354056937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1682306819432232876843445039826530000000000000)
      constant := (47231549731034457347217933462809296739249134383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree089.table
  base := (-363612803521326658493055119731291441367/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 68820500000000000000000000000000000000000000
      center := (175112)
      previous := (0)
      next := (100170)
      square := (733055977627279207949582967908000000000000)
      linear := (-84994612966339781975696684392186500000000000)
      constant := (2412287396034687088688131929655283314718804753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree089.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel089

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14103936171878672899/3125000000000000000)
  centralHi := (451325957500117532769/100000000000000000000)
  directionLo := (14183845798164696343/3125000000000000000)
  directionHi := (453883065541270282977/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree090.table
  base := (-729140126483439505677394025564211508323/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137641000000000000000000000000000000000000000
      center := (346514)
      previous := (0)
      next := (204050)
      square := (1466111955254558415899165935816000000000000)
      linear := (-170076165186090885474708144122885000000000000)
      constant := (4829352676375987829815381957521741363782913957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree090.table
  base := (-1822859477520402533215347784407957577569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (875560)
      previous := (0)
      next := (500850)
      square := (3665279888136396039747914839540000000000000)
      linear := (-429636170241942518856275917390212500000000000)
      constant := (12332593342665443491996416164830804311065825271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree090.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel090

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14183845798164696343/3125000000000000000)
  centralHi := (453883065541270282977/100000000000000000000)
  directionLo := (456425847709005425559/100000000000000000000)
  directionHi := (11410646192725135639/2500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree091.table
  base := (-365469688310191966104338101397663980031/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9831500000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (104722282518182743992797566844000000000000)
      linear := (-12280117744925605947505127447365500000000000)
      constant := (352623451926619889758096400252532983160650447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree091.table
  base := (-7309426121905343157318532859552139529443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (500320)
      previous := (0)
      next := (286200)
      square := (2094445650363654879855951336880000000000000)
      linear := (-248171014658392073048039093039710000000000000)
      constant := (7203861180724120127513346859005706280432562291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree091.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel091

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (456425847709005425559/100000000000000000000)
  centralHi := (11410646192725135639/2500000000000000000)
  directionLo := (229477271057847563033/50000000000000000000)
  directionHi := (458954542115695126067/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree092.table
  base := (-1831548188918169346842832967645307651427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-434417829179565202638588561008372500000000000)
      constant := (12613204788823507982942289066714667209549936293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree092.table
  base := (-7326221321030724936764864873829163429739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1755849524249718947247443632995090000000000000)
      constant := (51535712519247422300255444214096320116367294301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree092.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel092

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229477271057847563033/50000000000000000000)
  centralHi := (458954542115695126067/100000000000000000000)
  directionLo := (14420918135929291269/3125000000000000000)
  directionHi := (461469380349737320609/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree093.table
  base := (-734179883092743806899800415037127512749/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137641000000000000000000000000000000000000000
      center := (346514)
      previous := (0)
      next := (204050)
      square := (1466111955254558415899165935816000000000000)
      linear := (-175612614914693678845799064543581000000000000)
      constant := (5155013433819544888224676832432261232017714891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree093.table
  base := (-183545601185626096469886576565236972673/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34410250000000000000000000000000000000000000
      center := (87556)
      previous := (0)
      next := (50085)
      square := (366527988813639603974791483954000000000000)
      linear := (-44362548647267334578965340367805250000000000)
      constant := (1316410651471897016250368485574945217844315607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree093.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel093

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14420918135929291269/3125000000000000000)
  centralHi := (461469380349737320609/100000000000000000000)
  directionLo := (9279411754461889101/2000000000000000000)
  directionHi := (463970587723094455051/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree094.table
  base := (-7356212517404990404624240559673972530657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1774580981575612766361627046838130000000000000)
      constant := (52659228746109379326354121522949624746907839863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree094.table
  base := (-7356234775431831259895732826739832259023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1793154367531667819069783596429330000000000000)
      constant := (53789168818665097945186125954966462748035815257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree094.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel094

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9279411754461889101/2000000000000000000)
  centralHi := (463970587723094455051/100000000000000000000)
  directionLo := (466458383506885686867/100000000000000000000)
  directionHi := (116614595876721421717/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree095.table
  base := (-921179284670886784402097383503919053217/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-448258953501072186066315862060112500000000000)
      constant := (13445025578852413093078768270468492905192317806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree095.table
  base := (-230295435065334451813981085696624051/312500000000000000000000000000000000)
  polynomial :=
    { denominator := 34410250000000000000000000000000000000000000
      center := (87556)
      previous := (0)
      next := (50085)
      square := (366527988813639603974791483954000000000000)
      linear := (-45295169729316056374523839453661250000000000)
      constant := (1373348518530333112344682045204779775197047200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree095.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel095

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466458383506885686867/100000000000000000000)
  centralHi := (116614595876721421717/25000000000000000000)
  directionLo := (234466490577864880377/50000000000000000000)
  directionHi := (93786596231145952151/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree096.table
  base := (-1476292903564991881780203765120456274679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (2932223910509116831798331871632000000000000)
      linear := (-362298129286592944433779969928554000000000000)
      constant := (10982550998014967620388142987333727277896907761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree096.table
  base := (-7381481854392467335471333952239085129961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1830459210813616690892123559863570000000000000)
      constant := (56090741776007578232819442130708020083627037999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree096.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel096

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234466490577864880377/50000000000000000000)
  centralHi := (93786596231145952151/20000000000000000000)
  directionLo := (471394588521488185349/100000000000000000000)
  directionHi := (9427891770429763707/2000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree097.table
  base := (-739230359746034866310465582738223205343/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137641000000000000000000000000000000000000000
      center := (346514)
      previous := (0)
      next := (204050)
      square := (1466111955254558415899165935816000000000000)
      linear := (-182994547886164070007253625104509000000000000)
      constant := (5605718672073561999377184158288644719793384137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree097.table
  base := (-3696159447803245917821693380321595470863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-924555816227295563401646770790345000000000000)
      constant := (28629785939276370182228324668894775277794945817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree097.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel097

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471394588521488185349/100000000000000000000)
  centralHi := (9427891770429763707/2000000000000000000)
  directionLo := (236921704028507231419/50000000000000000000)
  directionHi := (473843408057014462839/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree098.table
  base := (-1850487958167742454371090176522060801729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49157500000000000000000000000000000000000000
      center := (123755)
      previous := (0)
      next := (72875)
      square := (523611412590913719963987834220000000000000)
      linear := (-66014296831797024213434737587407500000000000)
      constant := (2043335623708667898261026043498914218455602673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree098.table
  base := (-3700982665399781689252428453481150203583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (250160)
      previous := (0)
      next := (143100)
      square := (1047222825181827439927975668440000000000000)
      linear := (-133411718149683254479604537378415000000000000)
      constant := (4174316500686566657245054460102360143546947471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree098.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel098

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236921704028507231419/50000000000000000000)
  centralHi := (473843408057014462839/100000000000000000000)
  directionLo := (23813981850523731591/5000000000000000000)
  directionHi := (476279637010474631821/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree099.table
  base := (-3705204751425769781215974093907477536271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-933427571859496327939904526924865000000000000)
      constant := (29190693590469956687284579035601848384430123289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree099.table
  base := (-7410421411650098075024027698717906939547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1886416475736539998625633505014930000000000000)
      constant := (59633319134543887871811995958907928570933811373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree099.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel099

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23813981850523731591/5000000000000000000)
  centralHi := (476279637010474631821/100000000000000000000)
  directionLo := (186993542035455853/39062500000000000)
  directionHi := (478703467610766983681/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree100.table
  base := (-148353537100153110205727274066961188013/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137641000000000000000000000000000000000000000
      center := (346514)
      previous := (0)
      next := (204050)
      square := (1466111955254558415899165935816000000000000)
      linear := (-188530997614766863378344545525205000000000000)
      constant := (5956115583802915920259318335454996975603513335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree100.table
  base := (-7417687360648120411541703273647158813377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1905068897377514434536803486732050000000000000)
      constant := (60838236222724854915275915267891931413767976343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree100.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel100

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186993542035455853/39062500000000000)
  centralHi := (478703467610766983681/100000000000000000000)
  directionLo := (15034846476391694973/3125000000000000000)
  directionHi := (481115087244534239137/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree101.table
  base := (-1855938526946800221597188023950391155723/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-475941202144086152921770464163592500000000000)
      constant := (15188175851253881335090406137664340460935130557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree101.table
  base := (-3711881687379891199093383524125480909181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-961860659509244435223986734224585000000000000)
      constant := (31027591123522108101498185363027224682179417979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree101.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel101

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15034846476391694973/3125000000000000000)
  centralHi := (481115087244534239137/100000000000000000000)
  directionLo := (483514678625229484829/100000000000000000000)
  directionHi := (48351467862522948483/10000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree102.table
  base := (-3714320727501596357131808464682225315847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-961109820502510294795359129028345000000000000)
      constant := (30978014927611197155869772732223668825301503073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree102.table
  base := (-3714324814312519996896357982634282360349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-971186870329731653179571725083145000000000000)
      constant := (31642078591732176778421780490349954741639203291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree102.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel102

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483514678625229484829/100000000000000000000)
  centralHi := (48351467862522948483/10000000000000000000)
  directionLo := (242951209977333776389/50000000000000000000)
  directionHi := (485902419954667552779/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree103.table
  base := (-7432339068712560103775695754771420740993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-1940674473433696567494354659459010000000000000)
      constant := (63171135164967678337116053754699221877788982487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree103.table
  base := (-929043284668533926073989281165738264857/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-245128270287554717783789178985426250000000000)
      constant := (8065645126329568156947861648448321619486817663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree103.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel103

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242951209977333776389/50000000000000000000)
  centralHi := (485902419954667552779/100000000000000000000)
  directionLo := (244139242538733040481/50000000000000000000)
  directionHi := (488278485077466080963/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree104.table
  base := (-1486969420381424877369320007560100037107/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (2932223910509116831798331871632000000000000)
      linear := (-391825861172474509079598212172266000000000000)
      constant := (12879603862638686027308825379530372270792555413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree104.table
  base := (-743485345893393249352967012995408424503/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137641000000000000000000000000000000000000000
      center := (350224)
      previous := (0)
      next := (200340)
      square := (1466111955254558415899165935816000000000000)
      linear := (-197967858394141217818148341360053000000000000)
      constant := (6577819370956571999143440417669354989042982577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree104.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel104

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244139242538733040481/50000000000000000000)
  centralHi := (488278485077466080963/100000000000000000000)
  directionLo := (490643043628755042633/100000000000000000000)
  directionHi := (245321521814377521317/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree105.table
  base := (-3718082845432945367559802106020879092463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (247510)
      previous := (0)
      next := (145750)
      square := (1047222825181827439927975668440000000000000)
      linear := (-141256009877932037378687675875975000000000000)
      constant := (4688334448653005082799543782642248954404900031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree105.table
  base := (-1859042824103162375772316515124283498389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49157500000000000000000000000000000000000000
      center := (125080)
      previous := (0)
      next := (71550)
      square := (523611412590913719963987834220000000000000)
      linear := (-71368964485085236217594764118487500000000000)
      constant := (2394401973689922119146598588137861213571177093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree105.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel105

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490643043628755042633/100000000000000000000)
  centralHi := (245321521814377521317/50000000000000000000)
  directionLo := (123249065293877478091/25000000000000000000)
  directionHi := (98599252235101982473/20000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree106.table
  base := (-7436294957211515484238120538172022454999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25970000000000000000000000000000000000000000
      center := (65380)
      previous := (0)
      next := (38500)
      square := (276624897217841210547012440720000000000000)
      linear := (-37661112655089141532174789880490000000000000)
      constant := (1262021208529685610648494660863137257684367597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree106.table
  base := (-1859074974924329862379642445758423851349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6492500000000000000000000000000000000000000
      center := (16520)
      previous := (0)
      next := (9450)
      square := (69156224304460302636753110180000000000000)
      linear := (-9514072769921514386810487627522500000000000)
      constant := (322265781399831708641184685364145373258046647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree106.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel106

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123249065293877478091/25000000000000000000)
  centralHi := (98599252235101982473/20000000000000000000)
  directionLo := (19813531974073668023/4000000000000000000)
  directionHi := (15479321854745053143/3125000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree107.table
  base := (-148704700194167328398601596221905943311/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137641000000000000000000000000000000000000000
      center := (346514)
      previous := (0)
      next := (204050)
      square := (1466111955254558415899165935816000000000000)
      linear := (-201449380314840047910890026506829000000000000)
      constant := (6814934461101679240567856098137484720283653245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree107.table
  base := (-7435239367203710513867740316574364761741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-2035635848864335485914993358751890000000000000)
      constant := (69609464876359183930705657727174027859829207019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree107.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel107

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19813531974073668023/4000000000000000000)
  centralHi := (15479321854745053143/3125000000000000000)
  directionLo := (24883465799427835029/5000000000000000000)
  directionHi := (497669315988556700581/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree108.table
  base := (-7432985945834841919401272202981823780193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-2032948635577076457012536666470610000000000000)
      constant := (69423343944555412052081662658789518793070455287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree108.table
  base := (-7432989787265631802290861225274205432197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-2054288270505309921826163340469010000000000000)
      constant := (70910612909944050613248119541931873090106972723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree108.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel108

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24883465799427835029/5000000000000000000)
  centralHi := (497669315988556700581/100000000000000000000)
  directionLo := (99997893047455966073/20000000000000000000)
  directionHi := (249994732618639915183/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree109.table
  base := (-7429547853158469638676475200174171297417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-2051403468005752434916173067872930000000000000)
      constant := (70709122040636314229476615659992611888452226703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree109.table
  base := (-7429551239370888215502134801608692904113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-2072940692146284357737333322186130000000000000)
      constant := (72223789746578141325219335223733737899984982567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree109.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel109

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99997893047455966073/20000000000000000000)
  centralHi := (249994732618639915183/50000000000000000000)
  directionLo := (100459779537883560669/20000000000000000000)
  directionHi := (251149448844708901673/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree110.table
  base := (-371246040526934427975063555526825592479/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 68820500000000000000000000000000000000000000
      center := (173257)
      previous := (0)
      next := (102025)
      square := (733055977627279207949582967908000000000000)
      linear := (-103492915021721420640990473463762500000000000)
      constant := (3600333944420260344848848814527369698625597961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree110.table
  base := (-7424923795240878532856471643142800623927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-2091593113787258793648503303903250000000000000)
      constant := (73548995376389651017230115523020181779322063793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree110.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel110

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100459779537883560669/20000000000000000000)
  centralHi := (251149448844708901673/50000000000000000000)
  directionLo := (25229888024511096301/5000000000000000000)
  directionHi := (504597760490221926021/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree111.table
  base := (-1854776222294765477942028277611344312197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-522078283215776097680861467669392500000000000)
      constant := (18329003619515390102014279350701055707524892723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree111.table
  base := (-370955375988688442040835389337805695253/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 68820500000000000000000000000000000000000000
      center := (175112)
      previous := (0)
      next := (100170)
      square := (733055977627279207949582967908000000000000)
      linear := (-105512276771411661477983664281018500000000000)
      constant := (3744311489522296560548681461241953086299681827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree111.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel111

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25229888024511096301/5000000000000000000)
  centralHi := (504597760490221926021/100000000000000000000)
  directionLo := (506886197448195002349/100000000000000000000)
  directionHi := (10137723948963900047/2000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree112.table
  base := (-3706050076773956892501180095201758708047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (247510)
      previous := (0)
      next := (145750)
      square := (1047222825181827439927975668440000000000000)
      linear := (-150483426092270026330505876577135000000000000)
      constant := (5331223485766563583336477075710807818523671839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree112.table
  base := (-7412102471868623366857156177892732615303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (500320)
      previous := (0)
      next := (286200)
      square := (2094445650363654879855951336880000000000000)
      linear := (-304128279581315380781549038191070000000000000)
      constant := (10890784711520007972445154917295215198585297111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree112.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel112

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506886197448195002349/100000000000000000000)
  centralHi := (10137723948963900047/2000000000000000000)
  directionLo := (101832869828014507869/20000000000000000000)
  directionHi := (254582174570036269673/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree113.table
  base := (-296156266487359110646450373218254791403/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (2932223910509116831798331871632000000000000)
      linear := (-425044559544091269306143734696442000000000000)
      constant := (15194004369671773268659055766081643961282498385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree113.table
  base := (-1850977176286413021614623219685912129161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (875560)
      previous := (0)
      next := (500850)
      square := (3665279888136396039747914839540000000000000)
      linear := (-536887594677545525345503312263652500000000000)
      constant := (19399196234897921371105586344456621368630150799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree113.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel113

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101832869828014507869/20000000000000000000)
  centralHi := (254582174570036269673/50000000000000000000)
  directionLo := (255716176505797558803/50000000000000000000)
  directionHi := (511432353011595117607/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree114.table
  base := (-739452446840154694239831358527001289503/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137641000000000000000000000000000000000000000
      center := (346514)
      previous := (0)
      next := (204050)
      square := (1466111955254558415899165935816000000000000)
      linear := (-214367763014913232443435507488453000000000000)
      constant := (7731469361360425632300202140022766015511517577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree114.table
  base := (-7394526268575796933337208922482434389683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3502240)
      previous := (0)
      next := (2003400)
      square := (14661119552545584158991659358160000000000000)
      linear := (-2166202800351156537293183230771730000000000000)
      constant := (78970105660560410824193740552821955248169642197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree114.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel114

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255716176505797558803/50000000000000000000)
  centralHi := (511432353011595117607/100000000000000000000)
  directionLo := (513690343474276342647/100000000000000000000)
  directionHi := (64211292934284542831/12500000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree115.table
  base := (-7383953620907782096137020150857295919403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-2162132462577808302337991476286850000000000000)
      constant := (78671144089763957788577354191853225932357451677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree115.table
  base := (-1476791041406237864407216781897026504663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (700448)
      previous := (0)
      next := (400680)
      square := (2932223910509116831798331871632000000000000)
      linear := (-436971044398426194640870642497770000000000000)
      constant := (16071091027473997357280237443815511374871680017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree115.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel115

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513690343474276342647/100000000000000000000)
  centralHi := (64211292934284542831/12500000000000000000)
  directionLo := (806153831247436191/156250000000000000)
  directionHi := (515938451998359162241/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree116.table
  base := (-7372194164343234915055914109999445576551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-2180587295006484280241627877689170000000000000)
      constant := (80039373270693600565177515957955826311397943809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree116.table
  base := (-294887822470661560410194579040031891141/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (700448)
      previous := (0)
      next := (400680)
      square := (2932223910509116831798331871632000000000000)
      linear := (-440701528726621081823104638841194000000000000)
      constant := (16350566672868414773057026909966666852357308095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree116.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel116

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (806153831247436191/156250000000000000)
  centralHi := (515938451998359162241/100000000000000000000)
  directionLo := (259088403601071230643/50000000000000000000)
  directionHi := (518176807202142461287/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree117.table
  base := (-147184922795104918410703501155559510677/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137641000000000000000000000000000000000000000
      center := (346514)
      previous := (0)
      next := (204050)
      square := (1466111955254558415899165935816000000000000)
      linear := (-219904212743516025814526427909149000000000000)
      constant := (8141938115074338765609921739888884666954535215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree117.table
  base := (-1471849474168046049617139873640650619539/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275282000000000000000000000000000000000000000
      center := (700448)
      previous := (0)
      next := (400680)
      square := (2932223910509116831798331871632000000000000)
      linear := (-444432013054815969005338635184618000000000000)
      constant := (16632448067247655598855729819903435208076032501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree117.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel117

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259088403601071230643/50000000000000000000)
  centralHi := (518176807202142461287/100000000000000000000)
  directionLo := (520405534937849673581/100000000000000000000)
  directionHi := (260202767468924836791/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree118.table
  base := (-3672554792506328379704926754327313450323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-1108748479931918118024450340246905000000000000)
      constant := (41405583862350506914115217663395629249384091957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree118.table
  base := (-918138833685347680526707141168632861649/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-280101560864381785117232894705026250000000000)
      constant := (10572959506026179423636488668595838204289769991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree118.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel118

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (520405534937849673581/100000000000000000000)
  centralHi := (260202767468924836791/50000000000000000000)
  directionLo := (522624758374201628473/100000000000000000000)
  directionHi := (261312379187100814237/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree119.table
  base := (-7329784535169210985243187689120636615827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (495020)
      previous := (0)
      next := (291500)
      square := (2094445650363654879855951336880000000000000)
      linear := (-319421684613216030564648154556590000000000000)
      constant := (12030676141105949537873596009847225922222993699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree119.table
  base := (-732978549041934811706523832729033457551/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19663000000000000000000000000000000000000000
      center := (50032)
      previous := (0)
      next := (28620)
      square := (209444565036365487985595133688000000000000)
      linear := (-32278070122228981669271901990819000000000000)
      constant := (1228816292796446041700188190470317015124174687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree119.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel119

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (522624758374201628473/100000000000000000000)
  centralHi := (261312379187100814237/50000000000000000000)
  directionLo := (52483459807584693293/10000000000000000000)
  directionHi := (524834598075846932931/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree120.table
  base := (-7313271022782086835383418483933923319649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-2254406624721188191856173483298450000000000000)
      constant := (85630076935384083896986578401687850860360191991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree120.table
  base := (-1828317966038024326756908408891275020127/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (875560)
      previous := (0)
      next := (500850)
      square := (3665279888136396039747914839540000000000000)
      linear := (-569529332549250788190050780268612500000000000)
      constant := (21865658418666322952609126935121796014954699593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree120.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel120

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52483459807584693293/10000000000000000000)
  centralHi := (524834598075846932931/100000000000000000000)
  directionLo := (105407034415958966593/20000000000000000000)
  directionHi := (263517586039897416483/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree121.table
  base := (-7295569078191192655516537467743251979921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-2272861457149864169759809884700770000000000000)
      constant := (87057199563452309899236088758736836054231693639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree121.table
  base := (-729556981920753888894183552864775362019/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137641000000000000000000000000000000000000000
      center := (350224)
      previous := (0)
      next := (200340)
      square := (1466111955254558415899165935816000000000000)
      linear := (-229676975183797758867137310279157000000000000)
      constant := (8892015558102522471767892352628255454396342821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree121.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel121

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105407034415958966593/20000000000000000000)
  centralHi := (263517586039897416483/50000000000000000000)
  directionLo := (529226595968987663049/100000000000000000000)
  directionHi := (10584531919379753261/2000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree122.table
  base := (-909584841220518198335827878020199106561/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-572829072394635036915861571525772500000000000)
      constant := (22124025217010444395238313786819666049547674798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree122.table
  base := (-454792461397078211818796824892291611497/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-289427771684869003072817885563586250000000000)
      constant := (11298713276393338170600367365851530180603882846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree122.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel122

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529226595968987663049/100000000000000000000)
  centralHi := (10584531919379753261/2000000000000000000)
  directionLo := (531408982943142641499/100000000000000000000)
  directionHi := (1062817965886285283/200000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree123.table
  base := (-3628300002055616934164417984810873831573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-1154885561003608062783541343752705000000000000)
      constant := (44973390422744910129286991298689354014948460707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree123.table
  base := (-3628300289393937410080128980368009586677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-1167037297559963230246856533112905000000000000)
      constant := (45935642780780683870913292753269786792480191043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree123.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel123

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531408982943142641499/100000000000000000000)
  centralHi := (1062817965886285283/200000000000000000)
  directionLo := (266791221943492935087/50000000000000000000)
  directionHi := (21343297755479434807/4000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree124.table
  base := (-452208307892132577692368149960382129491/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (866285)
      previous := (0)
      next := (510125)
      square := (3665279888136396039747914839540000000000000)
      linear := (-582056488608973025867679772226932500000000000)
      constant := (22852309873087419573224571606563427173258917076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree124.table
  base := (-904416679038468763232717038514458715627/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-294090877095112612050610380992866250000000000)
      constant := (11670611703624232460958147092374851387922384093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree124.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel124

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266791221943492935087/50000000000000000000)
  centralHi := (21343297755479434807/4000000000000000000)
  directionLo := (107149417487198983417/20000000000000000000)
  directionHi := (267873543717997458543/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree125.table
  base := (-7212877519891578541477145601777053488603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3465140)
      previous := (0)
      next := (2040500)
      square := (14661119552545584158991659358160000000000000)
      linear := (-2346680786864568081374355490310050000000000000)
      constant := (92883476805367687628039348118091429580775194477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree125.table
  base := (-3606438982726577320733115551564756948993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1751120)
      previous := (0)
      next := (1001700)
      square := (7330559776272792079495829679080000000000000)
      linear := (-1185689719200937666158026514830025000000000000)
      constant := (47435265205170857440678793436479575288783654487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree125.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel125

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107149417487198983417/20000000000000000000)
  centralHi := (267873543717997458543/50000000000000000000)
  directionLo := (268951510019880135951/50000000000000000000)
  directionHi := (537903020039760271903/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree126.table
  base := (-3594616903672556953351410607754561506617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (247510)
      previous := (0)
      next := (145750)
      square := (1047222825181827439927975668440000000000000)
      linear := (-168938258520946004234142277979455000000000000)
      constant := (6740678055818802507261589258971987057095389929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree126.table
  base := (-7189234199636708376911688086957909083539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (500320)
      previous := (0)
      next := (286200)
      square := (2094445650363654879855951336880000000000000)
      linear := (-341433122863264252603889001625310000000000000)
      constant := (13769742271808239842910629588379826633690372643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree126.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel126

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268951510019880135951/50000000000000000000)
  centralHi := (537903020039760271903/100000000000000000000)
  directionLo := (135012586505767560093/25000000000000000000)
  directionHi := (540050346023070240373/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree127.table
  base := (-3582200904943505861045565340344132226887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1732570)
      previous := (0)
      next := (1020250)
      square := (7330559776272792079495829679080000000000000)
      linear := (-1191795225860960018590814146557345000000000000)
      constant := (47933643708855567519480105597345250796159046433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree127.table
  base := (-895550269407024687753983763022876681163/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (437780)
      previous := (0)
      next := (250425)
      square := (1832639944068198019873957419770000000000000)
      linear := (-301085535210478025517299124136786250000000000)
      constant := (12239736262891772506970091065550823230728043517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree127.checked
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
end ForestUnimodality.Stage170KernelData.Cell316.Kernel127

namespace ForestUnimodality.Stage170KernelData.Cell316
open FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem degreePropagationThreshold : row.degreePropagationCheck 127 interval.lo interval.hi = true := by
  decide +kernel

theorem degreePropagationTail (n : ℕ) (hn : 127 ≤ n) (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual n j q :=
  row.degreePropagationCheck_sound 127 interval.lo interval.hi degreePropagationThreshold
    (fun _q hq j => Kernel127.actual_residual_nonneg j hq) n hn q hq j
end ForestUnimodality.Stage170KernelData.Cell316

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel128
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  degreePropagationTail 128 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel128

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel129
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  degreePropagationTail 129 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel129

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel130
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  degreePropagationTail 130 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel130

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel131
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  degreePropagationTail 131 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel131

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel132
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  degreePropagationTail 132 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel132

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel133
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  degreePropagationTail 133 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel133

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel134
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  degreePropagationTail 134 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel134

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel135
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  degreePropagationTail 135 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel135

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel136
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  degreePropagationTail 136 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel136

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel137
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  degreePropagationTail 137 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel137

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel138
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  degreePropagationTail 138 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel138

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel139
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  degreePropagationTail 139 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel139

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel140
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  degreePropagationTail 140 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel140

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel141
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  degreePropagationTail 141 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel141

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel142
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  degreePropagationTail 142 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel142

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel143
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  degreePropagationTail 143 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel143

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel144
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  degreePropagationTail 144 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel144

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel145
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  degreePropagationTail 145 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel145

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel146
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  degreePropagationTail 146 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel146

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel147
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  degreePropagationTail 147 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel147

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel148
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  degreePropagationTail 148 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel148

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel149
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  degreePropagationTail 149 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel149

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel150
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  degreePropagationTail 150 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel151
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  degreePropagationTail 151 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel152
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  degreePropagationTail 152 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel153
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  degreePropagationTail 153 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel154
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  degreePropagationTail 154 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel155
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  degreePropagationTail 155 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel156
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  degreePropagationTail 156 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel157
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  degreePropagationTail 157 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel158
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  degreePropagationTail 158 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel159
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  degreePropagationTail 159 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel160
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  degreePropagationTail 160 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel161
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  degreePropagationTail 161 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel162
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  degreePropagationTail 162 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel163
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  degreePropagationTail 163 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel164
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  degreePropagationTail 164 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel165
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  degreePropagationTail 165 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel166
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  degreePropagationTail 166 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel167
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  degreePropagationTail 167 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel168
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  degreePropagationTail 168 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel169
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  degreePropagationTail 169 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel170
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 170 j q :=
  degreePropagationTail 170 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel171
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 171 j q :=
  degreePropagationTail 171 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel172
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 172 j q :=
  degreePropagationTail 172 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel173
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 173 j q :=
  degreePropagationTail 173 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel174
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 174 j q :=
  degreePropagationTail 174 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel175
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 175 j q :=
  degreePropagationTail 175 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel176
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 176 j q :=
  degreePropagationTail 176 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel177
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 177 j q :=
  degreePropagationTail 177 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel178
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 178 j q :=
  degreePropagationTail 178 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel179
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 179 j q :=
  degreePropagationTail 179 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel180
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 180 j q :=
  degreePropagationTail 180 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel181
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 181 j q :=
  degreePropagationTail 181 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel182
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 182 j q :=
  degreePropagationTail 182 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel183
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 183 j q :=
  degreePropagationTail 183 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel184
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 184 j q :=
  degreePropagationTail 184 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel185
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 185 j q :=
  degreePropagationTail 185 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel186
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 186 j q :=
  degreePropagationTail 186 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel187
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 187 j q :=
  degreePropagationTail 187 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel188
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 188 j q :=
  degreePropagationTail 188 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel189
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 189 j q :=
  degreePropagationTail 189 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel190
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 190 j q :=
  degreePropagationTail 190 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel191
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 191 j q :=
  degreePropagationTail 191 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel192
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 192 j q :=
  degreePropagationTail 192 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel193
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 193 j q :=
  degreePropagationTail 193 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel194
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 194 j q :=
  degreePropagationTail 194 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel195
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 195 j q :=
  degreePropagationTail 195 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel196
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 196 j q :=
  degreePropagationTail 196 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel197
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 197 j q :=
  degreePropagationTail 197 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel198
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 198 j q :=
  degreePropagationTail 198 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel199
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 199 j q :=
  degreePropagationTail 199 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel199

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel200
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  degreePropagationTail 200 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel201
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  degreePropagationTail 201 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel202
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  degreePropagationTail 202 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel203
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  degreePropagationTail 203 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel204
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  degreePropagationTail 204 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel205
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  degreePropagationTail 205 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel206
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  degreePropagationTail 206 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel207
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  degreePropagationTail 207 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel208
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  degreePropagationTail 208 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel209
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  degreePropagationTail 209 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel210
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  degreePropagationTail 210 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel211
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  degreePropagationTail 211 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel212
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  degreePropagationTail 212 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel213
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  degreePropagationTail 213 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel214
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  degreePropagationTail 214 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel215
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  degreePropagationTail 215 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel216
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  degreePropagationTail 216 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel217
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  degreePropagationTail 217 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel218
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  degreePropagationTail 218 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel219
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  degreePropagationTail 219 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel220
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  degreePropagationTail 220 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel221
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  degreePropagationTail 221 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel222
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  degreePropagationTail 222 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel223
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  degreePropagationTail 223 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel224
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  degreePropagationTail 224 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel225
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  degreePropagationTail 225 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel226
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  degreePropagationTail 226 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel227
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  degreePropagationTail 227 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel228
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  degreePropagationTail 228 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel229
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  degreePropagationTail 229 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel230
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  degreePropagationTail 230 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel231
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  degreePropagationTail 231 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel232
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  degreePropagationTail 232 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel233
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  degreePropagationTail 233 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel234
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  degreePropagationTail 234 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel235
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  degreePropagationTail 235 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel236
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  degreePropagationTail 236 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel237
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  degreePropagationTail 237 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel238
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  degreePropagationTail 238 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel239
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  degreePropagationTail 239 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel240
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  degreePropagationTail 240 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel241
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  degreePropagationTail 241 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel242
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  degreePropagationTail 242 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel243
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  degreePropagationTail 243 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel244
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  degreePropagationTail 244 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel245
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  degreePropagationTail 245 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel246
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  degreePropagationTail 246 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel247
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  degreePropagationTail 247 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel248
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  degreePropagationTail 248 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel249
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  degreePropagationTail 249 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel249

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel250
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  degreePropagationTail 250 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel251
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  degreePropagationTail 251 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel252
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  degreePropagationTail 252 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel253
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  degreePropagationTail 253 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel254
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  degreePropagationTail 254 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel255
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  degreePropagationTail 255 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel256
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  degreePropagationTail 256 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel257
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  degreePropagationTail 257 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel258
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  degreePropagationTail 258 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel259
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  degreePropagationTail 259 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel260
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  degreePropagationTail 260 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel261
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  degreePropagationTail 261 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel262
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  degreePropagationTail 262 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel263
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  degreePropagationTail 263 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel264
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  degreePropagationTail 264 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel265
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  degreePropagationTail 265 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel266
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  degreePropagationTail 266 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel267
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  degreePropagationTail 267 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel268
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  degreePropagationTail 268 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel269
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  degreePropagationTail 269 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel270
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  degreePropagationTail 270 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel271
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  degreePropagationTail 271 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel272
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  degreePropagationTail 272 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel273
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  degreePropagationTail 273 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel274
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  degreePropagationTail 274 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel275
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  degreePropagationTail 275 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel276
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  degreePropagationTail 276 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel277
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  degreePropagationTail 277 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel278
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  degreePropagationTail 278 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel279
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  degreePropagationTail 279 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel280
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  degreePropagationTail 280 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel281
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  degreePropagationTail 281 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel282
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  degreePropagationTail 282 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel283
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  degreePropagationTail 283 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel284
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  degreePropagationTail 284 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel285
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  degreePropagationTail 285 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel286
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  degreePropagationTail 286 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel287
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  degreePropagationTail 287 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel288
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  degreePropagationTail 288 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel289
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  degreePropagationTail 289 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel290
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  degreePropagationTail 290 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel291
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  degreePropagationTail 291 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel292
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  degreePropagationTail 292 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel293
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  degreePropagationTail 293 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel294
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  degreePropagationTail 294 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel295
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  degreePropagationTail 295 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel296
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  degreePropagationTail 296 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel297
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  degreePropagationTail 297 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel298
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  degreePropagationTail 298 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel299
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  degreePropagationTail 299 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel299

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel300
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 300 j q :=
  degreePropagationTail 300 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel301
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 301 j q :=
  degreePropagationTail 301 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel302
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 302 j q :=
  degreePropagationTail 302 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel303
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 303 j q :=
  degreePropagationTail 303 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel304
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 304 j q :=
  degreePropagationTail 304 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel305
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 305 j q :=
  degreePropagationTail 305 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel306
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 306 j q :=
  degreePropagationTail 306 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel307
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 307 j q :=
  degreePropagationTail 307 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel308
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 308 j q :=
  degreePropagationTail 308 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel309
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 309 j q :=
  degreePropagationTail 309 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel310
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 310 j q :=
  degreePropagationTail 310 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel311
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 311 j q :=
  degreePropagationTail 311 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel312
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 312 j q :=
  degreePropagationTail 312 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel313
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 313 j q :=
  degreePropagationTail 313 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel314
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 314 j q :=
  degreePropagationTail 314 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel315
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 315 j q :=
  degreePropagationTail 315 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel316
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 316 j q :=
  degreePropagationTail 316 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel317
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 317 j q :=
  degreePropagationTail 317 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel318
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 318 j q :=
  degreePropagationTail 318 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel319
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 319 j q :=
  degreePropagationTail 319 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel320
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 320 j q :=
  degreePropagationTail 320 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel321
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 321 j q :=
  degreePropagationTail 321 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel322
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 322 j q :=
  degreePropagationTail 322 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel323
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 323 j q :=
  degreePropagationTail 323 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel324
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 324 j q :=
  degreePropagationTail 324 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel325
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 325 j q :=
  degreePropagationTail 325 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel326
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 326 j q :=
  degreePropagationTail 326 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel327
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 327 j q :=
  degreePropagationTail 327 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel328
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 328 j q :=
  degreePropagationTail 328 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel329
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 329 j q :=
  degreePropagationTail 329 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel330
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 330 j q :=
  degreePropagationTail 330 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel331
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 331 j q :=
  degreePropagationTail 331 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel332
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 332 j q :=
  degreePropagationTail 332 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel333
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 333 j q :=
  degreePropagationTail 333 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel334
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 334 j q :=
  degreePropagationTail 334 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel335
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 335 j q :=
  degreePropagationTail 335 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel336
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 336 j q :=
  degreePropagationTail 336 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel337
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 337 j q :=
  degreePropagationTail 337 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel338
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 338 j q :=
  degreePropagationTail 338 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel339
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 339 j q :=
  degreePropagationTail 339 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel340
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 340 j q :=
  degreePropagationTail 340 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel341
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 341 j q :=
  degreePropagationTail 341 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel342
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 342 j q :=
  degreePropagationTail 342 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel343
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 343 j q :=
  degreePropagationTail 343 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel344
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 344 j q :=
  degreePropagationTail 344 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel345
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 345 j q :=
  degreePropagationTail 345 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel346
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 346 j q :=
  degreePropagationTail 346 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel347
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 347 j q :=
  degreePropagationTail 347 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel348
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 348 j q :=
  degreePropagationTail 348 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell316.Kernel349
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 127 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 349 j q :=
  degreePropagationTail 349 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell316.Kernel349

