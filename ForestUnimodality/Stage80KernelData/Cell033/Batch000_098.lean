import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell033.Parameters
import ForestUnimodality.BinomialMassData.Q841_1786.Batch000_049
import ForestUnimodality.BinomialMassData.Q841_1786.Batch050_099
import ForestUnimodality.BinomialMassData.Q1687_3572.Batch000_049
import ForestUnimodality.BinomialMassData.Q1687_3572.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree000.table
  base := (2546041893842643318912166697/50000000000000000000000000)
  polynomial :=
    { denominator := 1786000000000000000000000000000000000000000
      center := (10395)
      previous := (9251)
      next := (0)
      square := (351670634422829310294922324280000000000000)
      linear := (1488730777463265107174450469000000000000000)
      constant := (90944616448059219351542594416840000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree000.table
  base := (2546041893842643318912166697/50000000000000000000000000)
  polynomial :=
    { denominator := 3572000000000000000000000000000000000000000
      center := (20735)
      previous := (18557)
      next := (0)
      square := (703341268845658620589844648560000000000000)
      linear := (2977461554926530214348900938000000000000000)
      constant := (181889232896118438703085188833680000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree001.table
  base := (305078779432092082721941201916172209288619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (5168407903625481453743772970487600000000000000)
      constant := (240502877354307649696626002595563062124999932931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree001.table
  base := (152237977799127487892624844549911412595037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (10328024041390392174730172882868200000000000000)
      constant := (480029849107873924624073442482947499249998642452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49915157706522119783/100000000000000000000)
  directionHi := (6239394713315264973/12500000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree002.table
  base := (190751076094017834389679846477789487830883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (3689632885877484203953624596890200000000000000)
      constant := (147246806899192459480271220390865549281249817467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree002.table
  base := (190079792524607869740728723824939568118149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (7361682240033826942392503077566400000000000000)
      constant := (293402350950327724429286385225036567312499603802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49915157706522119783/100000000000000000000)
  centralHi := (6239394713315264973/12500000000000000000)
  directionLo := (70590692996555495851/100000000000000000000)
  directionHi := (17647673249138873963/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree003.table
  base := (62533575314720577117818569983896016169881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (2210857868129486954163476223292800000000000000)
      constant := (93478000934683562129930711915031838397310867138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree003.table
  base := (124493605611988428596793641112025482336259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (4395340438677261710054833272264600000000000000)
      constant := (186022743212211386616391008273496692727134806582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70590692996555495851/100000000000000000000)
  centralHi := (17647673249138873963/25000000000000000000)
  directionLo := (86455589215509506557/100000000000000000000)
  directionHi := (43227794607754753279/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree004.table
  base := (85957690428076275824422767147669136888467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (732082850381489704373327849695400000000000000)
      constant := (61597308189021183487468905671426805542571120683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree004.table
  base := (1710159108492937582308943984289406442801/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3189796000000000000000000000000000000000000000
      center := (18516355)
      previous := (16571401)
      next := (0)
      square := (628083753079173148186731271164080000000000000)
      linear := (285799727464139295543432693392560000000000000)
      constant := (24493847071265293869530397352228537568104292980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86455589215509506557/100000000000000000000)
  centralHi := (43227794607754753279/50000000000000000000)
  directionLo := (99830315413044239567/100000000000000000000)
  directionHi := (6239394713315264973/6250000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree005.table
  base := (61558900049184640980014697280745173708381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-746692167366507545416820523902000000000000000)
      constant := (42143956851783801073975209271119208028574720069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree005.table
  base := (12242815984281549888667134439831494612977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3189796000000000000000000000000000000000000000
      center := (18516355)
      previous := (16571401)
      next := (0)
      square := (628083753079173148186731271164080000000000000)
      linear := (-307468632807173750924101267667800000000000000)
      constant := (16749713324145258983019833980939746095247791346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99830315413044239567/100000000000000000000)
  centralHi := (6239394713315264973/6250000000000000000)
  directionLo := (111613685739405957607/100000000000000000000)
  directionHi := (13951710717425744701/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree006.table
  base := (45467825934328921952678969399710124090863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-2225467185114504795206968897499400000000000000)
      constant := (30011918010749126312752025274688638746134608487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree006.table
  base := (11300187669301549660617902897171464523013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-4503684965392433986958176143640800000000000000)
      constant := (59635481612731798636418252102454797699297550696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111613685739405957607/100000000000000000000)
  centralHi := (13951710717425744701/12500000000000000000)
  directionLo := (12226666681153063719/10000000000000000000)
  directionHi := (122266666811530637191/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree007.table
  base := (34205856774471424451076481998012244700031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-3704242202862502044997117271096800000000000000)
      constant := (22427176556136358928865278524836916523795020919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree007.table
  base := (33993190739172375330608653061382122072909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-7470026766748999219295845948942600000000000000)
      constant := (44588065519764760281767271390502698729838418282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12226666681153063719/10000000000000000000)
  centralHi := (122266666811530637191/100000000000000000000)
  directionLo := (132063093944026701179/100000000000000000000)
  directionHi := (6603154697201335059/5000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree008.table
  base := (5172809913224907099400135327771103516567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (9282735)
      previous := (8261143)
      next := (0)
      square := (314041876539586574093365635582040000000000000)
      linear := (-1036603444122099858957453128938840000000000000)
      constant := (3573489559751461088091425440539898728182837583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree008.table
  base := (642220033869039491974184656041744816577/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3189796000000000000000000000000000000000000000
      center := (18516355)
      previous := (16571401)
      next := (0)
      square := (628083753079173148186731271164080000000000000)
      linear := (-2087273713621112890326703150848880000000000000)
      constant := (7114373479317828636725120743931253795752193168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132063093944026701179/100000000000000000000)
  centralHi := (6603154697201335059/5000000000000000000)
  directionLo := (141181385993110991703/100000000000000000000)
  directionHi := (17647673249138873963/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree009.table
  base := (19378736078221427170197001995312232776409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-6661792238358496544577414018291600000000000000)
      constant := (15484510571415954989348499607169194715314580641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree009.table
  base := (961475743889377731677418250178565054497/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3189796000000000000000000000000000000000000000
      center := (18516355)
      previous := (16571401)
      next := (0)
      square := (628083753079173148186731271164080000000000000)
      linear := (-2680542073892425936794237111909240000000000000)
      constant := (6179875454087555667816728092497227193148625224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141181385993110991703/100000000000000000000)
  centralHi := (17647673249138873963/12500000000000000000)
  directionLo := (149745473119566359351/100000000000000000000)
  directionHi := (18718184139945794919/12500000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree010.table
  base := (565751265376484969797224212819762586427/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (9282735)
      previous := (8261143)
      next := (0)
      square := (314041876539586574093365635582040000000000000)
      linear := (-1628113451221298758873512478377800000000000000)
      constant := (2959000676518339236350472630018534273918123615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree010.table
  base := (7006654263425160525332195600435710767801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-16369052170818694916308855364848000000000000000)
      constant := (29610430211301401811832956669989928464288558596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149745473119566359351/100000000000000000000)
  centralHi := (18718184139945794919/12500000000000000000)
  directionLo := (157845588119116416599/100000000000000000000)
  directionHi := (789227940595582083/500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree011.table
  base := (2450676921856237305849182302211392303011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-9619342273854491044157710765486400000000000000)
      constant := (15514652771241277068721811843167140322575275756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree011.table
  base := (1210806727305892301131431328174200677433/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-19335393972175260148646525170149800000000000000)
      constant := (31140865368298459749990618609575285496292294672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157845588119116416599/100000000000000000000)
  centralHi := (789227940595582083/500000000000000000)
  directionLo := (41387462365987661669/25000000000000000000)
  directionHi := (165549849463950646677/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree012.table
  base := (1534239211286319906374650818042380882349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-11098117291602488293947859139083800000000000000)
      constant := (17469170363580284068126156237095114368993310804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree012.table
  base := (1206425149724589956692573192786987730151/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3189796000000000000000000000000000000000000000
      center := (18516355)
      previous := (16571401)
      next := (0)
      square := (628083753079173148186731271164080000000000000)
      linear := (-4460347154706365076196838995090320000000000000)
      constant := (7028973795254207954718910225553901156842369598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41387462365987661669/25000000000000000000)
  centralHi := (165549849463950646677/100000000000000000000)
  directionLo := (86455589215509506557/50000000000000000000)
  directionHi := (34582235686203802623/20000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree013.table
  base := (3005589350261715589918806377357068047743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-12576892309350485543738007512681200000000000000)
      constant := (20546163891080498671957680166700066557604607607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree013.table
  base := (45475434967247630537343891130354916733/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-25268077574888390613321864780753400000000000000)
      constant := (41399320419899166844024082150923805943208206976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86455589215509506557/50000000000000000000)
  centralHi := (34582235686203802623/20000000000000000000)
  directionLo := (89985830266868501771/50000000000000000000)
  directionHi := (179971660533737003543/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree014.table
  base := (19532983178115174068894831358904030517/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-14055667327098482793528155886278600000000000000)
      constant := (24669016469833268595932163512988426563708018128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree014.table
  base := (112943698972313168239679406824652082173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-28234419376244955845659534586055200000000000000)
      constant := (49751950499486445754834451716118547913107106708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89985830266868501771/50000000000000000000)
  centralHi := (179971660533737003543/100000000000000000000)
  directionLo := (93382709272297358089/50000000000000000000)
  directionHi := (186765418544594716179/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree015.table
  base := (-1005706507211638129494514408384934668277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-15534442344846480043318304259876000000000000000)
      constant := (29782556589710644187505141744846934467434349254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree015.table
  base := (-1045170995432686754769452856911108254237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-31200761177601521077997204391357000000000000000)
      constant := (60092956198088678496428700815523249535067834348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93382709272297358089/50000000000000000000)
  centralHi := (186765418544594716179/100000000000000000000)
  directionLo := (96660287260338486019/50000000000000000000)
  directionHi := (193320574520676972039/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree016.table
  base := (-4018533964970135691248843904312212309391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-17013217362594477293108452633473400000000000000)
      constant := (35845076807236211400135552925393330606088456441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree016.table
  base := (-4090377798041921751759834853447814264843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-34167102978958086310334874196658800000000000000)
      constant := (72339215467810101621293169910384187924630428986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96660287260338486019/50000000000000000000)
  centralHi := (193320574520676972039/100000000000000000000)
  directionLo := (39932126165217695827/20000000000000000000)
  directionHi := (6239394713315264973/3125000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree017.table
  base := (-2874976090861072505511905657800782109101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-18491992380342474542898601007070800000000000000)
      constant := (42823788363287278659978883760091898215759033302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree017.table
  base := (-2907619910059447773166404697733821860457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-37133444780314651542672544001960600000000000000)
      constant := (86425305917198427520839523877108920964801703228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39932126165217695827/20000000000000000000)
  centralHi := (6239394713315264973/3125000000000000000)
  directionLo := (205805467543354075021/100000000000000000000)
  directionHi := (102902733771677037511/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree018.table
  base := (-7238950116176753893562344592614187676523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-19970767398090471792688749380668200000000000000)
      constant := (50692150200199656220957962118307208651544410173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree018.table
  base := (-3649079417622666052379159154798317780427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-40099786581671216775010213807262400000000000000)
      constant := (102298227844645313044520055858877045137265077108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205805467543354075021/100000000000000000000)
  centralHi := (102902733771677037511/50000000000000000000)
  directionLo := (42354415797933297511/20000000000000000000)
  directionHi := (52943019747416621889/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree019.table
  base := (-68104215640557145043859727659363681601/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 83942000000000000000000000000000000000000000
      center := (488565)
      previous := (434797)
      next := (0)
      square := (16528519817872977583861349241160000000000000)
      linear := (-225784657008825989920830502676480000000000000)
      constant := (625560348621159601805029345232331172988110725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree019.table
  base := (-4283302320018976746948603001384904102429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4872725)
      previous := (4360895)
      next := (0)
      square := (165285198178729775838613492411600000000000000)
      linear := (-2266638335948830631965678084871800000000000000)
      constant := (6311272090866649547439080991197721759667809764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42354415797933297511/20000000000000000000)
  centralHi := (52943019747416621889/25000000000000000000)
  directionLo := (217575128193625377759/100000000000000000000)
  directionHi := (1359844551210158611/625000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree020.table
  base := (-4797609914794208407591430092550163027141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-22928317433586466292269046127863000000000000000)
      constant := (69013666182490372814861673021181930088338873382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree020.table
  base := (-241089862468954061367236704269824095963/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3189796000000000000000000000000000000000000000
      center := (18516355)
      previous := (16571401)
      next := (0)
      square := (628083753079173148186731271164080000000000000)
      linear := (-9206494036876869447937110683573200000000000000)
      constant := (27847284274785105976517451108699728711974425808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217575128193625377759/100000000000000000000)
  centralHi := (1359844551210158611/625000000000000000)
  directionLo := (111613685739405957607/50000000000000000000)
  directionHi := (44645474295762383043/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree021.table
  base := (-2626250829078559915996792060220767800281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-24407092451334463542059194501460400000000000000)
      constant := (79432919409020214929242046626557485753734867324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree021.table
  base := (-2637146515984757143108767951301018505287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-48998811985740912472023223223167800000000000000)
      constant := (160233949815913190872798459236232907751819097096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111613685739405957607/50000000000000000000)
  centralHi := (44645474295762383043/20000000000000000000)
  directionLo := (114369994257897978033/50000000000000000000)
  directionHi := (228739988515795956067/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree022.table
  base := (-2814734096818484306094838103915800614973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-25885867469082460791849342875057800000000000000)
      constant := (90672787862915868508603370368286594861561584492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree022.table
  base := (-11298121249615728545133318472326033633269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-51965153787097477704360893028469600000000000000)
      constant := (182880372386818449126690459841434253610366538438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114369994257897978033/50000000000000000000)
  centralHi := (228739988515795956067/100000000000000000000)
  directionLo := (14632677647546453987/6250000000000000000)
  directionHi := (234122842360743263793/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree023.table
  base := (-1483893872997325945136900146591983229611/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-27364642486830458041639491248655200000000000000)
      constant := (102722002041551249912320154472103006524239501288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree023.table
  base := (-5953156818404092314986140312456630031757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-54931495588454042936698562833771400000000000000)
      constant := (207153179364499792676118514980349566351221648428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14632677647546453987/6250000000000000000)
  centralHi := (234122842360743263793/100000000000000000000)
  directionLo := (239384686820064609993/100000000000000000000)
  directionHi := (119692343410032304997/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree024.table
  base := (-12353735815774678546887069393669364225713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-28843417504578455291429639622252600000000000000)
      constant := (115570921815746759579693906290054959167569393863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree024.table
  base := (-6192616042559761058944628202897421203389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-57897837389810608169036232639073200000000000000)
      constant := (233033122148913916200817309719577017435114581356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239384686820064609993/100000000000000000000)
  centralHi := (119692343410032304997/50000000000000000000)
  directionLo := (244533333623061274381/100000000000000000000)
  directionHi := (122266666811530637191/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree025.table
  base := (-12717046853270218584888029532981222973571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-30322192522326452541219787995850000000000000000)
      constant := (129211288827096963970714560326359906720948779621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree025.table
  base := (-6372605749045464787510633095272267314433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-60864179191167173401373902444375000000000000000)
      constant := (260503717623072785139032042536154777809490874332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244533333623061274381/100000000000000000000)
  centralHi := (122266666811530637191/50000000000000000000)
  directionLo := (249575788532610598919/100000000000000000000)
  directionHi := (6239394713315264973/2500000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree026.table
  base := (-12969963770731189156791438135587773200081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-31800967540074449791009936369447400000000000000)
      constant := (143636021988238146367767231097630865849368606631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree026.table
  base := (-12995109711009729075551980442850062674101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-63830520992523738633711572249676800000000000000)
      constant := (289550838443192320089291325774888220741201663302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249575788532610598919/100000000000000000000)
  centralHi := (6239394713315264973/2500000000000000000)
  directionLo := (254518363169617564421/100000000000000000000)
  directionHi := (127259181584808782211/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree027.table
  base := (-6406301134316397232575172954160005227/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-33279742557822447040800084743044800000000000000)
      constant := (158839046209145600775207638594094312767071389696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree027.table
  base := (-13142522738950459439758347753621624121913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-66796862793880303866049242054978600000000000000)
      constant := (320162369740022169236213094682031853931209200126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254518363169617564421/100000000000000000000)
  centralHi := (127259181584808782211/50000000000000000000)
  directionLo := (259366767646528519671/100000000000000000000)
  directionHi := (32420845955816064959/12500000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree028.table
  base := (-1646750984877280580788198999520835684749/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-34758517575570444290590233116642200000000000000)
      constant := (174815147633726365951588573810403672832260757592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree028.table
  base := (-13193966736132741571542750966232673987349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-69763204595236869098386911860280400000000000000)
      constant := (352327918912229767639405246665455040722925054598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259366767646528519671/100000000000000000000)
  centralHi := (32420845955816064959/12500000000000000000)
  directionLo := (264126187888053402359/100000000000000000000)
  directionHi := (6603154697201335059/2500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree029.table
  base := (-13137285760025951386836963644787935078167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-36237292593318441540380381490239600000000000000)
      constant := (191559850562338758997291015157308955959850804017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree029.table
  base := (-13155032688255989808690437824307264719793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-72729546396593434330724581665582200000000000000)
      constant := (386038568907905090770362765669347267112931583886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264126187888053402359/100000000000000000000)
  centralHi := (6603154697201335059/2500000000000000000)
  directionLo := (268801350623731543759/100000000000000000000)
  directionHi := (3360016882796644297/1250000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree030.table
  base := (-203355577333599496199878130283197439201/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-37716067611066438790170529863837000000000000000)
      constant := (209069312420590830885581015107742847059622512064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree030.table
  base := (-3257629599006687067504701983406008126733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-75695888197949999563062251470884000000000000000)
      constant := (421286667724296872827072018697251397802759167064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268801350623731543759/100000000000000000000)
  centralHi := (3360016882796644297/1250000000000000000)
  directionLo := (136698289186449986231/50000000000000000000)
  directionHi := (273396578372899972463/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree031.table
  base := (-12810558753504803531626930736520345751353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-39194842628814436039960678237434400000000000000)
      constant := (227340233917540849249331258042143036800929301503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree031.table
  base := (-12824541337344589317549114042096322604093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-78662229999306564795399921276185800000000000000)
      constant := (458065648404138041648490033784025934271377282486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136698289186449986231/50000000000000000000)
  centralHi := (273396578372899972463/100000000000000000000)
  directionLo := (277915836243414188639/100000000000000000000)
  directionHi := (1736973976521338679/625000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree032.table
  base := (-12528243712902603141894510346099014628021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-40673617646562433289750826611031800000000000000)
      constant := (246369782083388732985741401165506486883899281571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree032.table
  base := (-1254063531432902825501588768546817513003/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3189796000000000000000000000000000000000000000
      center := (18516355)
      previous := (16571401)
      next := (0)
      square := (628083753079173148186731271164080000000000000)
      linear := (-16325714360132626005547518216297520000000000000)
      constant := (99273974978699157303144242810475155684293082612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277915836243414188639/100000000000000000000)
  centralHi := (1736973976521338679/625000000000000000)
  directionLo := (282362771986221983407/100000000000000000000)
  directionHi := (17647673249138873963/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree033.table
  base := (-1521357794134612662210837200463270746381/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-42152392664310430539540974984629200000000000000)
      constant := (266155524279598609353383481804129171652553743448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree033.table
  base := (-761364580468930651491519888721641514731/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-84594913602019695260075260886789400000000000000)
      constant := (536194509929698174337345309889103577263016920992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282362771986221983407/100000000000000000000)
  centralHi := (17647673249138873963/6250000000000000000)
  directionLo := (28674075045694178529/10000000000000000000)
  directionHi := (286740750456941785291/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree034.table
  base := (-11741034178872589131338857289939238257377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-43631167682058427789331123358226600000000000000)
      constant := (286695371584651424763667795649088444390892968727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree034.table
  base := (-11750738410037882470016229178264639491433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-87561255403376260492412930692091200000000000000)
      constant := (577535401748957956527194896783584983004392491166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28674075045694178529/10000000000000000000)
  centralHi := (286740750456941785291/100000000000000000000)
  directionLo := (291052883410347156819/100000000000000000000)
  directionHi := (14552644170517357841/5000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree035.table
  base := (-11241008603780361209309129175065970677207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-45109942699806425039121271731824000000000000000)
      constant := (307987530206008438325266865598724066749431955057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree035.table
  base := (-224991699273231706462510992066862019181/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3189796000000000000000000000000000000000000000
      center := (18516355)
      previous := (16571401)
      next := (0)
      square := (628083753079173148186731271164080000000000000)
      linear := (-18105519440946565144950120099478600000000000000)
      constant := (124077797379963275543145356523007833993322614620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291052883410347156819/100000000000000000000)
  centralHi := (14552644170517357841/5000000000000000000)
  directionLo := (29530205537778451057/10000000000000000000)
  directionHi := (295302055377784510571/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree036.table
  base := (-10672717252939482305949099644929469922903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-46588717717554422288911420105421400000000000000)
      constant := (330030459771133968483138793441231839139450925553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree036.table
  base := (-2670072660708526492063477064417704568891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-93493939006089390957088270302694800000000000000)
      constant := (664752206855214402192680145792791727273939527528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29530205537778451057/10000000000000000000)
  centralHi := (295302055377784510571/100000000000000000000)
  directionLo := (299490946239132718703/100000000000000000000)
  directionHi := (18718184139945794919/6250000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree037.table
  base := (-627363679208115086298157063797923312507/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-48067492735302419538701568479018800000000000000)
      constant := (352822837518692343766409898179385607637833685712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree037.table
  base := (-627781338839984841503854454942079855589/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-96460280807445956189425940107996600000000000000)
      constant := (710622436454695886829423685684357062559693041248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299490946239132718703/100000000000000000000)
  centralHi := (18718184139945794919/6250000000000000000)
  directionLo := (60724410198231833929/20000000000000000000)
  directionHi := (151811025495579584823/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree038.table
  base := (-933773785910868972163202936085810086539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 83942000000000000000000000000000000000000000
      center := (488565)
      previous := (434797)
      next := (0)
      square := (16528519817872977583861349241160000000000000)
      linear := (-521539660558425439878860177395960000000000000)
      constant := (3961721342659296592556090307456524929715743262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree038.table
  base := (-9343630057425380957783811199905640984667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4872725)
      previous := (4360895)
      next := (0)
      square := (165285198178729775838613492411600000000000000)
      linear := (-5232980137305395864303347890173600000000000000)
      constant := (39894601183865101609153402056201420684465082686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60724410198231833929/20000000000000000000)
  centralHi := (151811025495579584823/50000000000000000000)
  directionLo := (153848848563244887123/50000000000000000000)
  directionHi := (307697697126489774247/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree039.table
  base := (-857369741750534643678945867964523621283/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (9282735)
      previous := (8261143)
      next := (0)
      square := (314041876539586574093365635582040000000000000)
      linear := (-10205008554159682807656373045242720000000000000)
      constant := (80130310888385746953767069817595607205462985866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree039.table
  base := (-134045142799699094407907749938262503261/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-102392964410159086654101279718600200000000000000)
      constant := (806875231016639873061909659970005035644738407808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153848848563244887123/50000000000000000000)
  centralHi := (307697697126489774247/100000000000000000000)
  directionLo := (311720059966971018867/100000000000000000000)
  directionHi := (77930014991742754717/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree040.table
  base := (-1549349587289306393477037957643541777141/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (9282735)
      previous := (8261143)
      next := (0)
      square := (314041876539586574093365635582040000000000000)
      linear := (-10500763557709282257614402719962200000000000000)
      constant := (85137216110198509981072330200639115253360686691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree040.table
  base := (-3875659724142832017111061858766764434267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-105359306211515651886438949523902000000000000000)
      constant := (857254202083844617244463313248093209874632860468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311720059966971018867/100000000000000000000)
  centralHi := (77930014991742754717/25000000000000000000)
  directionLo := (315691176238232833199/100000000000000000000)
  directionHi := (789227940595582083/250000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree041.table
  base := (-1371558285102561968621702098520066085481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (9282735)
      previous := (8261143)
      next := (0)
      square := (314041876539586574093365635582040000000000000)
      linear := (-10796518561258881707572432394681680000000000000)
      constant := (90293277314637322179244058416479161820199262031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree041.table
  base := (-1372362860580304305765951077530357846347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3189796000000000000000000000000000000000000000
      center := (18516355)
      previous := (16571401)
      next := (0)
      square := (628083753079173148186731271164080000000000000)
      linear := (-21665129602574443423755323865840760000000000000)
      constant := (181826582188740444620648233950353042331576862394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315691176238232833199/100000000000000000000)
  centralHi := (789227940595582083/250000000000000000)
  directionLo := (319612956125914828613/100000000000000000000)
  directionHi := (159806478062957414307/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree042.table
  base := (-5907602472028061673201736733099995654643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-55461367824042405787652310347005800000000000000)
      constant := (477991854814624075676002596721296941565200594293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree042.table
  base := (-5911140451650175822732733655659456637179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-111291989814228782351114289134505600000000000000)
      constant := (962510134710369181299693533937208143928276487258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319612956125914828613/100000000000000000000)
  centralHi := (159806478062957414307/50000000000000000000)
  directionLo := (323487194016104649471/100000000000000000000)
  directionHi := (1263621851625408787/390625000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree043.table
  base := (-4896846241693218975625414032447156089717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-56940142841790403037442458720603200000000000000)
      constant := (505261954839581902106642445853343097823411268067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree043.table
  base := (-306247250432301465747926198303013871417/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-114258331615585347583451958939807400000000000000)
      constant := (1017384823761718566648890043213198191520076312544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323487194016104649471/100000000000000000000)
  centralHi := (1263621851625408787/390625000000000000)
  directionLo := (163657789045679022259/50000000000000000000)
  directionHi := (327315578091358044519/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree044.table
  base := (-956523484056292561597158502585347336391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-58418917859538400287232607094200600000000000000)
      constant := (533276231143822159173885885375496469407769333764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree044.table
  base := (-957206459287158903741883683622402719061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-117224673416941912815789628745109200000000000000)
      constant := (1073756077190193722700788279144602388592700196888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163657789045679022259/50000000000000000000)
  centralHi := (327315578091358044519/100000000000000000000)
  directionLo := (41387462365987661669/12500000000000000000)
  directionHi := (331099698927901293353/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree045.table
  base := (-2695836067296550265622332107596574966893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-59897692877286397537022755467798000000000000000)
      constant := (562034292569302015944952280951415468889226144043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree045.table
  base := (-2698234778226315892650922427184470936201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-120191015218298478048127298550411000000000000000)
      constant := (1131623121732018187075592408039585216672794897502) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41387462365987661669/12500000000000000000)
  centralHi := (331099698927901293353/100000000000000000000)
  directionLo := (334841057218217872821/100000000000000000000)
  directionHi := (167420528609108936411/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree046.table
  base := (-753246927644400901873662493573838917233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-61376467895034394786812903841395400000000000000)
      constant := (591535803214249511264012322754059271458582922766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree046.table
  base := (-754299486471387902434754969534299563269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-123157357019655043280464968355712800000000000000)
      constant := (1190985293681883830776112673193394269390282796876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334841057218217872821/100000000000000000000)
  centralHi := (167420528609108936411/50000000000000000000)
  directionLo := (338541070725371266579/100000000000000000000)
  directionHi := (16927053536268563329/5000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree047.table
  base := (-258429017774251374176243579169036062883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169670000000000000000000000000000000000000000
      center := (987525)
      previous := (878845)
      next := (0)
      square := (33408710270168784478017620806600000000000000)
      linear := (-1337345593888987064608575579042400000000000000)
      constant := (13229371800581878955856843014059388965121064139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree047.table
  base := (-52055120764817450108473885988633766861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67868000000000000000000000000000000000000000
      center := (393965)
      previous := (352583)
      next := (0)
      square := (13363484108067513791207048322640000000000000)
      linear := (-536696590727708972394904843238360000000000000)
      constant := (5326987333489762496948539762793646701755338826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338541070725371266579/100000000000000000000)
  centralHi := (16927053536268563329/5000000000000000000)
  directionLo := (342201080560462001241/100000000000000000000)
  directionHi := (171100540280231000621/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree048.table
  base := (65502989049263639746335871392798775497/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-64334017930530389286393200588590200000000000000)
      constant := (652768059104624099309000565604249855851540914448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree048.table
  base := (8371430024473502413147036484987164893/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3189796000000000000000000000000000000000000000
      center := (18516355)
      previous := (16571401)
      next := (0)
      square := (628083753079173148186731271164080000000000000)
      linear := (-25818008124473634749028061593263280000000000000)
      constant := (262838564367817493590647954329900946482837897850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342201080560462001241/100000000000000000000)
  centralHi := (171100540280231000621/50000000000000000000)
  directionLo := (86455589215509506557/25000000000000000000)
  directionHi := (345822356862038026229/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree049.table
  base := (2412669930799129815782057297550698193269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-65812792948278386536183348962187600000000000000)
      constant := (684498343933255114912905189033387956723524170781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree049.table
  base := (2411250957900367540517798567798346077239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-132056382423724738977477977771618200000000000000)
      constant := (1378037269407712277079840142854702721561896326622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86455589215509506557/25000000000000000000)
  centralHi := (345822356862038026229/100000000000000000000)
  directionLo := (349406103945654838487/100000000000000000000)
  directionHi := (43675762993206854811/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree050.table
  base := (1917604119479442198188983536929596724769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-67291567966026383785973497335785000000000000000)
      constant := (716971146448537053838781057376331939957140628562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree050.table
  base := (1916982576440344530478202150837039409107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-135022724225081304209815647576920000000000000000)
      constant := (1443375005855785184842850729721993884959011872172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349406103945654838487/100000000000000000000)
  centralHi := (43675762993206854811/12500000000000000000)
  directionLo := (352953464982777479259/100000000000000000000)
  directionHi := (17647673249138873963/5000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree051.table
  base := (5315466045353650980245136066327627474661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-68770342983774381035763645709382400000000000000)
      constant := (750186309789130535471515578469515350202040939789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree051.table
  base := (5314377479867250182907358740237716605031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-137989066026437869442153317382221800000000000000)
      constant := (1510205721999357741821111215893745928737930731838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352953464982777479259/100000000000000000000)
  centralHi := (17647673249138873963/5000000000000000000)
  directionLo := (11139547695642399703/3125000000000000000)
  directionHi := (356465526260556790497/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree052.table
  base := (6853274432487354900116750046572436553557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-70249118001522378285553794082979800000000000000)
      constant := (784143699251947232563771498573327942957197476093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree052.table
  base := (6852321546538092741759651995351758111353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-140955407827794434674490987187523600000000000000)
      constant := (1578529152459648441581799830921388128308280676994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11139547695642399703/3125000000000000000)
  centralHi := (356465526260556790497/100000000000000000000)
  directionLo := (71988664213494801417/20000000000000000000)
  directionHi := (179971660533737003543/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree053.table
  base := (1056061043004401888984063748468138774943/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-71727893019270375535343942456577200000000000000)
      constant := (818843199161966004796696129349108400383516163256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree053.table
  base := (8447654534892734186233731414500504042341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-143921749629150999906828656992825400000000000000)
      constant := (1648345069456513950504845918838528499896121576218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71988664213494801417/20000000000000000000)
  centralHi := (179971660533737003543/50000000000000000000)
  directionLo := (363387833244248357777/100000000000000000000)
  directionHi := (181693916622124178889/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree054.table
  base := (10100983214100317459394751406207659549193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-73206668037018372785134090830174600000000000000)
      constant := (854284710184236923873407595372044091899844408657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree054.table
  base := (2525063465282793300269374044807577290999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-146888091430507565139166326798127200000000000000)
      constant := (1719653277481296814092556534554016961625038892408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363387833244248357777/100000000000000000000)
  centralHi := (181693916622124178889/50000000000000000000)
  directionLo := (366800000434591911571/100000000000000000000)
  directionHi := (91700000108647977893/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree055.table
  base := (11810652072640833923839153525550363392577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-74685443054766370034924239203772000000000000000)
      constant := (890468147015607104082106511883307861737047136073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree055.table
  base := (5905007154390129610337548682644820137227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-149854433231864130371503996603429000000000000000)
      constant := (1792453608724454437454132091850262591694446135692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366800000434591911571/100000000000000000000)
  centralHi := (91700000108647977893/25000000000000000000)
  directionLo := (46272589633281345743/12500000000000000000)
  directionHi := (74036143413250153189/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree056.table
  base := (10861922447840972378475066628194917267/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (9282735)
      previous := (8261143)
      next := (0)
      square := (314041876539586574093365635582040000000000000)
      linear := (-15232843614502873456942877515473880000000000000)
      constant := (185478687280505319540536857969632692144912970750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree056.table
  base := (1697105696001873392670577162534883638367/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-152820775033220695603841666408730800000000000000)
      constant := (1866745919151027539599752405555390886760514012528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46272589633281345743/12500000000000000000)
  centralHi := (74036143413250153189/20000000000000000000)
  directionLo := (373530837089189432357/100000000000000000000)
  directionHi := (186765418544594716179/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree057.table
  base := (3080231458276635714908134150305683820361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 83942000000000000000000000000000000000000000
      center := (488565)
      previous := (434797)
      next := (0)
      square := (16528519817872977583861349241160000000000000)
      linear := (-817294664108024889836889852115440000000000000)
      constant := (10158531741461793344529875180458469855624371531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree057.table
  base := (1925083765452832717922907012917505036661/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4872725)
      previous := (4360895)
      next := (0)
      square := (165285198178729775838613492411600000000000000)
      linear := (-8199321938661961096641017695475400000000000000)
      constant := (102238425533271495965726748719211594662299181296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373530837089189432357/100000000000000000000)
  centralHi := (186765418544594716179/50000000000000000000)
  directionLo := (37685117649467083787/10000000000000000000)
  directionHi := (376851176494670837871/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree058.table
  base := (17281847025852412749333101746471056700323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-79121768108010361784294684324564200000000000000)
      constant := (1003469330104219619808022355012352397694615876027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree058.table
  base := (17281421442212184113429546628228191391179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-158753458635933826068517006019334400000000000000)
      constant := (2019806000553874691826672868830539985993408604742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37685117649467083787/10000000000000000000)
  centralHi := (376851176494670837871/100000000000000000000)
  directionLo := (19007125781814338063/5000000000000000000)
  directionHi := (380142515636286761261/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree059.table
  base := (9609707045142148339063977276075327525991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-80600543125758359034084832698161600000000000000)
      constant := (1042619834008633787589248035511272437720547993918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree059.table
  base := (1201190151016854292147634291383337714113/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-161719800437290391300854675824636200000000000000)
      constant := (2098573574335516663954134765829219515857014327584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19007125781814338063/5000000000000000000)
  centralHi := (380142515636286761261/100000000000000000000)
  directionLo := (191702800685821684309/50000000000000000000)
  directionHi := (383405601371643368619/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree060.table
  base := (2651726066083671169368847153051799236207/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-82079318143506356283874981071759000000000000000)
      constant := (1082511987314743082404261862911902033992912287544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree060.table
  base := (2121348402866890307329556962196667165613/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3189796000000000000000000000000000000000000000
      center := (18516355)
      previous := (16571401)
      next := (0)
      square := (628083753079173148186731271164080000000000000)
      linear := (-32937228447729391306638469125987600000000000000)
      constant := (435766545659953555580400310062255080138203684948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191702800685821684309/50000000000000000000)
  centralHi := (383405601371643368619/100000000000000000000)
  directionLo := (96660287260338486019/25000000000000000000)
  directionHi := (386641149041353944077/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree061.table
  base := (2326498744116670079048542329263341934943/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (9282735)
      previous := (8261143)
      next := (0)
      square := (314041876539586574093365635582040000000000000)
      linear := (-16711618632250870706733025889071280000000000000)
      constant := (224629151162422450894802733105476935525356720814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree061.table
  base := (11632352103200659001370711968002535788629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-167652484040003521765530015435239800000000000000)
      constant := (2260583395344470812498898611105137891648425629684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96660287260338486019/25000000000000000000)
  centralHi := (386641149041353944077/100000000000000000000)
  directionLo := (38984984430019392849/10000000000000000000)
  directionHi := (389849844300193928491/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree062.table
  base := (12686456993665364338190025768703114732643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-85036868179002350783455277818953800000000000000)
      constant := (1164521110122364830581270575929149860280862855414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree062.table
  base := (25372666836715735923798465566095913539513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-170618825841360086997867685240541600000000000000)
      constant := (2343825517873471140190387428707049340312342204674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38984984430019392849/10000000000000000000)
  centralHi := (389849844300193928491/100000000000000000000)
  directionLo := (393032344813696501243/100000000000000000000)
  directionHi := (98258086203424125311/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree063.table
  base := (27537556530147693936340762136060533851539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-86515643196750348033245426192551200000000000000)
      constant := (1206638025016595825564401099997507386659375924011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree063.table
  base := (27537340922656725540752823662371772862729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-173585167642716652230205355045843400000000000000)
      constant := (2428559046449786537513796541926297890795220756642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393032344813696501243/100000000000000000000)
  centralHi := (98258086203424125311/25000000000000000000)
  directionLo := (396189281832080103539/100000000000000000000)
  directionHi := (19809464091604005177/5000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree064.table
  base := (7439721975247518087469015029783925676331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-87994418214498345283035574566148600000000000000)
      constant := (1249496478829210388861298515560555846986657918476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree064.table
  base := (29758699858250745816303488041421120274587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-176551509444073217462543024851145200000000000000)
      constant := (2514783938639603015815816644223380861883698257126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396189281832080103539/100000000000000000000)
  centralHi := (19809464091604005177/5000000000000000000)
  directionLo := (399321261652176958271/100000000000000000000)
  directionHi := (6239394713315264973/1562500000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree065.table
  base := (16018442384203702504977143244758001329157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-89473193232246342532825722939746000000000000000)
      constant := (1293096452954566683467009333182704296803869840986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree065.table
  base := (800918020159691864103537381398705928881/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3189796000000000000000000000000000000000000000
      center := (18516355)
      previous := (16571401)
      next := (0)
      square := (628083753079173148186731271164080000000000000)
      linear := (-35903570249085956538976138931289400000000000000)
      constant := (520500031604011863088349588482826641308483593104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399321261652176958271/100000000000000000000)
  centralHi := (6239394713315264973/1562500000000000000)
  directionLo := (201214433488476011671/50000000000000000000)
  directionHi := (402428866976952023343/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree066.table
  base := (34371527096084978478631318167369123594519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-90951968249994339782615871313343400000000000000)
      constant := (1337437931414725577465158449858063540241325582031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree066.table
  base := (34371384164847233183755514060576139348483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-182484193046786347927218364461748800000000000000)
      constant := (2691707673327613518492192115317965663494616839734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201214433488476011671/50000000000000000000)
  centralHi := (402428866976952023343/100000000000000000000)
  directionLo := (405512658181246324087/100000000000000000000)
  directionHi := (50689082272655790511/12500000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree067.table
  base := (7352559535474794506930337140283382638399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (9282735)
      previous := (8261143)
      next := (0)
      square := (314041876539586574093365635582040000000000000)
      linear := (-18486148653548467406481203937388160000000000000)
      constant := (276504180097652435163825182545636253201608644151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree067.table
  base := (7352534621596283686937513175772112999061/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3189796000000000000000000000000000000000000000
      center := (18516355)
      previous := (16571401)
      next := (0)
      square := (628083753079173148186731271164080000000000000)
      linear := (-37090106969628582631911206853410120000000000000)
      constant := (556481291545414655178989842763852886477976390778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405512658181246324087/100000000000000000000)
  centralHi := (50689082272655790511/12500000000000000000)
  directionLo := (408573174491531315787/100000000000000000000)
  directionHi := (102143293622882828947/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree068.table
  base := (4901335216947016763466821760703902726237/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-93909518285490334282196168060538200000000000000)
      constant := (1428345348391513233316269356147315332201079755304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree068.table
  base := (9802643298333388069411888295911014028643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-188416876649499478391893704072352400000000000000)
      constant := (2874596488184193316758511539952161137809018653656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408573174491531315787/100000000000000000000)
  centralHi := (102143293622882828947/25000000000000000000)
  directionLo := (205805467543354075021/50000000000000000000)
  directionHi := (411610935086708150043/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree069.table
  base := (41715166580694102512490706787471916785317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-95388293303238331531986316434135600000000000000)
      constant := (1474911265004853044675385786933868142568534256333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree069.table
  base := (41715072023993347952669521982231092058771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-191383218450856043624231373877654200000000000000)
      constant := (2968277744927166218549982913625613679262349750358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205805467543354075021/50000000000000000000)
  centralHi := (411610935086708150043/100000000000000000000)
  directionLo := (10365661003157892107/2500000000000000000)
  directionHi := (414626440126315684281/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree070.table
  base := (22138120657335356976346125480873710338529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-96867068320986328781776464807733000000000000000)
      constant := (1522218641637636822684337116013274518871499225042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree070.table
  base := (44276158958790987018611284685163737059623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-194349560252212608856569043682956000000000000000)
      constant := (3063450210984411520177222542137570773908918603454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10365661003157892107/2500000000000000000)
  centralHi := (414626440126315684281/100000000000000000000)
  directionLo := (104405042927978405781/25000000000000000000)
  directionHi := (668192274739061797/160000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree071.table
  base := (23446948289133723290002991988287194923961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-98345843338734326031566613181330400000000000000)
      constant := (1570267470826349167333691863330961720609835550978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree071.table
  base := (23446912431776048721143692522434267360899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-197315902053569174088906713488257800000000000000)
      constant := (3160113871787852784033247007689690011290726186604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104405042927978405781/25000000000000000000)
  centralHi := (668192274739061797/160000000000000000)
  directionLo := (420592594786873529097/100000000000000000000)
  directionHi := (210296297393436764549/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree072.table
  base := (49568124333699817513959488909583661843509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-99824618356482323281356761554927800000000000000)
      constant := (1619057746161266880534900180484603381553444408541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree072.table
  base := (49568061897595886498761198007211738317871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-200282243854925739321244383293559600000000000000)
      constant := (3258268714832403895162640336856383587019695822158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420592594786873529097/100000000000000000000)
  centralHi := (210296297393436764549/50000000000000000000)
  directionLo := (42354415797933297511/10000000000000000000)
  directionHi := (423544157979332975111/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree073.table
  base := (52298917677978497289792651051289951825559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-101303393374230320531146909928525200000000000000)
      constant := (1668589462137608024495618578759235170793340198991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree073.table
  base := (13074715832620743973051211003840762734817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-203248585656282304553582053098861400000000000000)
      constant := (3357914729383700550000143236188221974216936654664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42354415797933297511/10000000000000000000)
  centralHi := (423544157979332975111/100000000000000000000)
  directionLo := (426475294392640220679/100000000000000000000)
  directionHi := (10661882359816005517/2500000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree074.table
  base := (55086270682618475671864167576920764308999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-102782168391978317780937058302122600000000000000)
      constant := (1718862614027708156288445136858545086577446943551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree074.table
  base := (55086223384726989305384117805299105148841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-206214927457638869785919722904163200000000000000)
      constant := (3459051906227241281930151506178024832203676213218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426475294392640220679/100000000000000000000)
  centralHi := (10661882359816005517/2500000000000000000)
  directionLo := (13418325698351022617/3125000000000000000)
  directionHi := (85877284469446544749/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree075.table
  base := (57930178255991378222863327171928040365871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-104260943409726315030727206675720000000000000000)
      constant := (1769877197771253320346720865355458093861723463079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree075.table
  base := (57930137100791202133341556345275942011213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-209181269258995435018257392709465000000000000000)
      constant := (3561680237453070887953667698951389784361799591274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13418325698351022617/3125000000000000000)
  centralHi := (85877284469446544749/20000000000000000000)
  directionLo := (86455589215509506557/20000000000000000000)
  directionHi := (216138973038773766393/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree076.table
  base := (15207659006280558869499713001556400514953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 419710000000000000000000000000000000000000000
      center := (2442825)
      previous := (2173985)
      next := (0)
      square := (82642599089364887919306746205800000000000000)
      linear := (-5565248338288121698974597634174600000000000000)
      constant := (95875432099001000012932496028192094744052369452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree076.table
  base := (60830600221212782497288181470832939759429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4872725)
      previous := (4360895)
      next := (0)
      square := (165285198178729775838613492411600000000000000)
      linear := (-11165663740018526328978687500777200000000000000)
      constant := (192936827172156337496467106884830258629285989118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86455589215509506557/20000000000000000000)
  centralHi := (216138973038773766393/50000000000000000000)
  directionLo := (435150256387250755519/100000000000000000000)
  directionHi := (1359844551210158611/312500000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree077.table
  base := (63787640234183874437991898988688282846183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-107218493445222309530307503422914800000000000000)
      constant := (1874130647361924572704332900254945532467405787167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree077.table
  base := (63787609091144522446596915560063020638007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-215113952861708565482932732320068600000000000000)
      constant := (3771410336851831353101734276914155866489516088286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435150256387250755519/100000000000000000000)
  centralHi := (1359844551210158611/312500000000000000)
  directionLo := (427738018814251009/97656250000000000)
  directionHi := (438003731265793033217/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree078.table
  base := (66801187657330136311936546333156381197809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-108697268462970306780097651796512200000000000000)
      constant := (1927369507641522244240918156090894023029811589241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree078.table
  base := (33400580286493970987775318378172639264407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-218080294663065130715270402125370400000000000000)
      constant := (3878512094191504169396087211043651672035048390972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427738018814251009/97656250000000000)
  centralHi := (438003731265793033217/100000000000000000000)
  directionLo := (440838736469044897929/100000000000000000000)
  directionHi := (44083873646904489793/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree079.table
  base := (1746781888096058563359094133798556496469/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (9282735)
      previous := (8261143)
      next := (0)
      square := (314041876539586574093365635582040000000000000)
      linear := (-22035208696143660805977560034021920000000000000)
      constant := (396269957702061035070423696117105490636421660648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree079.table
  base := (13974250394624245404871190699435505556661/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3189796000000000000000000000000000000000000000
      center := (18516355)
      previous := (16571401)
      next := (0)
      square := (628083753079173148186731271164080000000000000)
      linear := (-44209327292884339189521614386134440000000000000)
      constant := (797420996798787363463119494516802143941307515578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440838736469044897929/100000000000000000000)
  centralHi := (44083873646904489793/10000000000000000000)
  directionLo := (110913906516634274193/25000000000000000000)
  directionHi := (443655626066537096773/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree080.table
  base := (36498950726924788353296854488215235892111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-111654818498466301279677948543707000000000000000)
      constant := (2036071488070447683626723028373825503293856049678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree080.table
  base := (18249470244752086112738097175747258060053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-224012978265778261179945741735974000000000000000)
      constant := (4097189002570870202674059090761979801541849638376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110913906516634274193/25000000000000000000)
  centralHi := (443655626066537096773/100000000000000000000)
  directionLo := (446454742957623830429/100000000000000000000)
  directionHi := (44645474295762383043/10000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree081.table
  base := (76181063403129073013485618443956524866531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-113133593516214298529468096917304400000000000000)
      constant := (2091534604691786368688213616521260136798290279419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree081.table
  base := (76181045605218478324196662698538847259853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-226979320067134826412283411541275800000000000000)
      constant := (4208764146755744688004523511110076485417045029994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446454742957623830429/100000000000000000000)
  centralHi := (44645474295762383043/10000000000000000000)
  directionLo := (224618209679349539027/50000000000000000000)
  directionHi := (89847283871739815611/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree082.table
  base := (3971037980785200610219651593954587674381/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (9282735)
      previous := (8261143)
      next := (0)
      square := (314041876539586574093365635582040000000000000)
      linear := (-22922473706792459155851649058180360000000000000)
      constant := (429547827394803854400396294930346527945389816276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree082.table
  base := (2481898254596666613791744779114692643477/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-229945661868491391644621081346577600000000000000)
      constant := (4321830413829804164733894071057750982166277771072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224618209679349539027/50000000000000000000)
  centralHi := (89847283871739815611/20000000000000000000)
  directionLo := (226000488631712870873/50000000000000000000)
  directionHi := (452000977263425741747/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree083.table
  base := (5169811786446076755232505212732672253179/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-116091143551710293029048393664499200000000000000)
      constant := (2204685083714244683822514875116607358090005445936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree083.table
  base := (82716975140978709943370231735595709402459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-232912003669847956876958751151879400000000000000)
      constant := (4436387801458669485427901118642579600734563054182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226000488631712870873/50000000000000000000)
  centralHi := (452000977263425741747/100000000000000000000)
  directionLo := (227374364438891224417/50000000000000000000)
  directionHi := (90949745775556489767/20000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree084.table
  base := (86069749009574931590988363042533828278093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-117569918569458290278838542038096600000000000000)
      constant := (2262372443879085295917324370359478758826536984757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree084.table
  base := (21517434332522582977894154947373835046617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-235878345471204522109296420957181200000000000000)
      constant := (4552436307637897913379875596918264939072717440264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227374364438891224417/50000000000000000000)
  centralHi := (90949745775556489767/20000000000000000000)
  directionLo := (114369994257897978033/25000000000000000000)
  directionHi := (457479977031591912133/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree085.table
  base := (44739519890864091028304461047439606050657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-119048693587206287528628690411694000000000000000)
      constant := (2320801216580749955838386922827965582810980747986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree085.table
  base := (89479029635215587737700305482613367415731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-238844687272561087341634090762483000000000000000)
      constant := (4669975930646255415631851714744195969464614540438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114369994257897978033/25000000000000000000)
  centralHi := (457479977031591912133/100000000000000000000)
  directionLo := (46019501556806635847/10000000000000000000)
  directionHi := (460195015568066358471/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree086.table
  base := (92944859943094581360291055790715848303609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-120527468604954284778418838785291400000000000000)
      constant := (2379971401056476782707074830293901762513864693441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree086.table
  base := (92944851129566070955232374950790124162491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-241811029073917652573971760567784800000000000000)
      constant := (4789006669005609016287207338416252167446508570918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46019501556806635847/10000000000000000000)
  centralHi := (460195015568066358471/100000000000000000000)
  directionLo := (462894129712788443137/100000000000000000000)
  directionHi := (231447064856394221569/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree087.table
  base := (96467208671821203088684110250229658828013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-122006243622702282028208987158888800000000000000)
      constant := (2439882996650879982207988027171483441202740138837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree087.table
  base := (96467201017192788897449746217282633734979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-244777370875274217806309430373086600000000000000)
      constant := (4909528521446501258839771157935890112978650537142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462894129712788443137/100000000000000000000)
  centralHi := (231447064856394221569/50000000000000000000)
  directionLo := (232788798211719579279/50000000000000000000)
  directionHi := (465577596423439158559/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree088.table
  base := (25011521315423596320624634733226455653331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-123485018640450279277999135532486200000000000000)
      constant := (2500536002800790175825353023861523615337172610476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree088.table
  base := (1250575982680741019890878419030959584571/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3189796000000000000000000000000000000000000000
      center := (18516355)
      previous := (16571401)
      next := (0)
      square := (628083753079173148186731271164080000000000000)
      linear := (-49548742535326156607729420035677680000000000000)
      constant := (1006308297375720344110278881039078550072209900128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232788798211719579279/50000000000000000000)
  centralHi := (465577596423439158559/100000000000000000000)
  directionLo := (93649136944297305517/20000000000000000000)
  directionHi := (234122842360743263793/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree089.table
  base := (103681489105814678391405953710250070780447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-124963793658198276527789283906083600000000000000)
      constant := (2561930419022236004414709997579342658693796679703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree089.table
  base := (103681483334139397576396676367138215313611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-250710054477987348270984769983690200000000000000)
      constant := (5155045564365344586910351868121092280327247556678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93649136944297305517/20000000000000000000)
  centralHi := (234122842360743263793/50000000000000000000)
  directionLo := (9417973120139189191/2000000000000000000)
  directionHi := (470898656006959459551/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree090.table
  base := (26843354920644409560144696609984047525239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-126442568675946273777579432279681000000000000000)
      constant := (2624066244899264525573286878937410674859817261244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree090.table
  base := (107373414671767860600501341012808976896939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-253676396279343913503322439788992000000000000000)
      constant := (5280040753102159197752358740216749511634974217222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9417973120139189191/2000000000000000000)
  centralHi := (470898656006959459551/100000000000000000000)
  directionLo := (473536764357349249799/100000000000000000000)
  directionHi := (2367683821786746249/500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree091.table
  base := (111121876543634737233488363300894676590231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-127921343693694271027369580653278400000000000000)
      constant := (2686943480074340654317759473525789608952203120719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree091.table
  base := (55560936096962224561246357142428917384127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-256642738080700478735660109594293800000000000000)
      constant := (5406527052397784508581971185507251465956218768092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473536764357349249799/100000000000000000000)
  centralHi := (2367683821786746249/500000000000000000)
  directionLo := (476160256811606112679/100000000000000000000)
  directionHi := (11904006420290152817/2500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree092.table
  base := (114926859303554680902146599974336178125213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-129400118711442268277159729026875800000000000000)
      constant := (2750562124240102590305925151492545210909772981637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree092.table
  base := (114926855528177833371904768838670393907407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-259609079882057043967997779399595600000000000000)
      constant := (5534504461658230536410932477912727333902135609486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476160256811606112679/100000000000000000000)
  centralHi := (11904006420290152817/2500000000000000000)
  directionLo := (239384686820064609993/50000000000000000000)
  directionHi := (478769373640129219987/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree093.table
  base := (59394183815472465294916498029146465067931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-130878893729190265526949877400473200000000000000)
      constant := (2814922177132281684978520806512628688843913016038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree093.table
  base := (14848545544306741259477421269851268690279/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-262575421683413609200335449204897400000000000000)
      constant := (5663972980373011765975432030530776464852708772336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239384686820064609993/50000000000000000000)
  centralHi := (478769373640129219987/100000000000000000000)
  directionLo := (481364348601585402619/100000000000000000000)
  directionHi := (24068217430079270131/5000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree094.table
  base := (61353200620413582387411472845667682271679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169670000000000000000000000000000000000000000
      center := (987525)
      previous := (878845)
      next := (0)
      square := (33408710270168784478017620806600000000000000)
      linear := (-2816120611636984314398723952639800000000000000)
      constant := (61277098691991962996092950497158487130207155186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree094.table
  base := (24541279679525390144945311549624475628171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67868000000000000000000000000000000000000000
      center := (393965)
      previous := (352583)
      next := (0)
      square := (13363484108067513791207048322640000000000000)
      linear := (-1129964950999022018862438804298720000000000000)
      constant := (24659287694056726074183955005891096955966354714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481364348601585402619/100000000000000000000)
  centralHi := (24068217430079270131/5000000000000000000)
  directionLo := (483945409187333451993/100000000000000000000)
  directionHi := (241972704593666725997/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree095.table
  base := (5067238395523581994378255691435714687719/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 83942000000000000000000000000000000000000000
      center := (488565)
      previous := (434797)
      next := (0)
      square := (16528519817872977583861349241160000000000000)
      linear := (-1408804671207223789752949201554400000000000000)
      constant := (31009121139143790855040508816718991905791270745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree095.table
  base := (15835119677644989328097828774746139317563/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 839420000000000000000000000000000000000000000
      center := (4872725)
      previous := (4360895)
      next := (0)
      square := (165285198178729775838613492411600000000000000)
      linear := (-14132005541375091561316357306079000000000000000)
      constant := (311967544445891303334193407041283548412758986768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483945409187333451993/100000000000000000000)
  centralHi := (241972704593666725997/50000000000000000000)
  directionLo := (486512776854177370009/100000000000000000000)
  directionHi := (48651277685417737001/10000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree096.table
  base := (65356021680931856652582349954047418903707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-135315218782434257276320322521265400000000000000)
      constant := (3012450786049238523403450779021365520314684486886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree096.table
  base := (1021187822044108920239757498039346998501/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-271474447087483304897348458620802800000000000000)
      constant := (6061325189154410947649975141914641081499551730944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486512776854177370009/100000000000000000000)
  centralHi := (48651277685417737001/10000000000000000000)
  directionLo := (244533333623061274381/50000000000000000000)
  directionHi := (489066667246122548763/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree097.table
  base := (134799651480695799280605106980508641411499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-136793993800182254526110470894862800000000000000)
      constant := (3079776471870657241461327543788470685584958466051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree097.table
  base := (67399824812061353511797638278978820603803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15948980000000000000000000000000000000000000000
      center := (92581775)
      previous := (82857005)
      next := (0)
      square := (3140418765395865740933656355820400000000000000)
      linear := (-274440788888839870129686128426104600000000000000)
      constant := (6196758141871712117799134753102523001046728394188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell033.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244533333623061274381/50000000000000000000)
  centralHi := (489066667246122548763/100000000000000000000)
  directionLo := (491607290405763340749/100000000000000000000)
  directionHi := (1966429161623053363/400000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree098.table
  base := (138943784088399438851597753355128103345241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (46413675)
      previous := (41305715)
      next := (0)
      square := (1570209382697932870466828177910200000000000000)
      linear := (-138272768817930251775900619268460200000000000000)
      constant := (3147843565558365621682285836594452350884559090209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree098.table
  base := (27788756495610103601848541802477258602479/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3189796000000000000000000000000000000000000000
      center := (18516355)
      previous := (16571401)
      next := (0)
      square := (628083753079173148186731271164080000000000000)
      linear := (-55481426138039287072404759646281280000000000000)
      constant := (1266736440476748563920905344306248994790576552142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell033.Kernel098
